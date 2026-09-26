"""Audit exactly the object just compiled, without re-elaborating its source."""
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
import hashlib, re, uuid


def digest(path: Path) -> str:
    if path.is_symlink() or not path.is_file():
        raise ValueError('Expected a private regular artifact: '+str(path))
    return hashlib.sha256(path.read_bytes()).hexdigest()


@dataclass(frozen=True)
class CompiledAudit:
    source: Path
    module: Path
    source_sha256: str
    bundle: dict[str, str]
    audit: Path
    audit_text: str

    def verify(self) -> None:
        if hashlib.sha256(self.source.read_bytes()).hexdigest()!=self.source_sha256:
            raise ValueError('Source changed across compilation or axiom audit')
        now={suffix:digest(Path(str(self.module)+suffix)) for suffix in
             ('','.private','.server') if Path(str(self.module)+suffix).exists() or Path(str(self.module)+suffix).is_symlink()}
        if now!=self.bundle or self.audit.read_text()!=self.audit_text:
            raise ValueError('Compiled artifact or axiom probe changed during audit')

def prepare_compiled_audit(source: Path, artifacts: Path, relative: str,
                           target: str, source_sha256: str) -> CompiledAudit:
    rel=PurePosixPath(relative)
    parts=rel.with_suffix('').parts
    if rel.is_absolute() or rel.suffix!='.lean' or not parts or any(
            not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*",p) for p in parts):
        raise ValueError('Invalid compiled Lean module path')
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*",target):
        raise ValueError('Invalid Lean axiom audit target')
    module=artifacts/Path(relative).with_suffix('.olean')
    if not module.resolve().is_relative_to(artifacts.resolve()):
        raise ValueError('Compiled module escaped private artifact namespace')
    bundle={'':digest(module)}
    for suffix in ('.private','.server'):
        path=Path(str(module)+suffix)
        if path.exists() or path.is_symlink():bundle[suffix]=digest(path)
    audit=artifacts/('Audit_'+uuid.uuid4().hex+'.lean')
    text='import '+'.'.join(parts)+'\n#print axioms '+target+'\n'
    audit.write_text(text)
    result=CompiledAudit(source,module,source_sha256,bundle,audit,text)
    result.verify()
    return result
