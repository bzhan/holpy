# Author: Bohua Zhan

unicode_table = {
    "\\lambda" : "λ",
    "%" : "λ",
    "\\forall" : "∀",
    "\\exists" : "∃",
    "\\and" : "∧",
    "&" : "∧",
    "\\or" : "∨",
    "|" : "∨",
    "-->" : "⟶",
    "~" : "¬",
    "\\not": "¬",
    "=>": "⇒"
}

def get_unicode_table_suffix(s):
    for k, v in unicode_table.items():
        if s.endswith(k):
            return v

    return None
