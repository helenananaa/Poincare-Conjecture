import unittest
from runtime import lean_code_without_comments,reconstruct,BEGIN,END
class CommentScanTests(unittest.TestCase):
    def test_line_comment_is_not_an_axiom(self):
        self.assertNotIn('axiom',lean_code_without_comments('by\n -- axiom from existing interface\n rfl'))
    def test_nested_blocks_are_masked(self):
        self.assertNotIn('sorry',lean_code_without_comments('by /- axiom /- sorry -/ safe -/ rfl'))
    def test_strings_cannot_hide_code(self):
        text='by let s := "-- not a comment"; sorry'
        self.assertIn('sorry',lean_code_without_comments(text))
    def test_real_placeholder_still_rejected(self):
        template='theorem t : True :=\n'+BEGIN+'\nby trivial\n'+END
        with self.assertRaises(ValueError):reconstruct(template,template.replace('by trivial','by /- comment -/ sorry'))
    def test_comment_only_change_keeps_proof_bytes(self):
        t='theorem t : True :=\n'+BEGIN+'\nby trivial\n'+END
        c=t.replace('by trivial','by\n -- no extra axiom is declared\n trivial')
        self.assertEqual(reconstruct(t,c),c)
    def test_unterminated_comment_is_rejected(self):
        with self.assertRaises(ValueError):lean_code_without_comments('by /- not closed')
