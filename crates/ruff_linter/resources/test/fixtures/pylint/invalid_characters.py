# ensures language of the file is detected as English in text editors
# (Pylint, "E1206") => Rule::LoggingTooFewArgs,
#        (Pylint, "E1307") => Rule::BadStringFormatType,
#        (Pylint, "E2502") => Rule::BidirectionalUnicode,
#        (Pylint, "E2510") => Rule::InvalidCharacterBackspace,
#        (Pylint, "E2511") => Rule::InvalidCharacterCarriageReturn,
#        (Pylint, "E2512") => Rule::InvalidCharacterSub,
#        (Pylint, "E2513") => Rule::InvalidCharacterEsc,
#        (Pylint, "E2514") => Rule::InvalidCharacterNul,
#        (Pylint, "E2515") => Rule::InvalidCharacterZeroWidthSpace,
#        (Pylint, "E1310") => Rule::BadStrStripCall,
#        (Pylint, "C0414") => Rule::UselessImportAlias,
#        (Pylint, "C3002") => Rule::UnnecessaryDirectLambdaCall,
#foo = 'hi'
b = ''
b = f''

b_ok = '\\b'
b_ok = f'\\b'

cr_ok = '\\r'
cr_ok = f'\\r'

sub = 'sub '
sub = f'sub '

sub_ok = '\x1a'
sub_ok = f'\x1a'

esc = 'esc esc '
esc = f'esc esc '

esc_ok = '\x1b'
esc_ok = f'\x1b'

nul = '''
nul  '''
nul = f'''
nul  '''

nul_ok = '\0'
nul_ok = f'\0'

zwsp = 'zero​width'
zwsp = f'zero​width'

zwsp_ok = '\u200b'
zwsp_ok = f'\u200b'

zwsp_after_multibyte_character = "ಫ​"
zwsp_after_multibyte_character = f"ಫ​"
zwsp_after_multicharacter_grapheme_cluster = "ಫ್ರಾನ್ಸಿಸ್ಕೊ ​​"
zwsp_after_multicharacter_grapheme_cluster = f"ಫ್ರಾನ್ಸಿಸ್ಕೊ ​​"

nested_fstrings = f'{f'{f''}'}'

# https://github.com/astral-sh/ruff/issues/7455#issuecomment-1741998106
x = f"""}}ab"""
# https://github.com/astral-sh/ruff/issues/7455#issuecomment-1741998256
x = f"""}}ab"""


# https://github.com/astral-sh/ruff/issues/13294
print(r""" ​
""")
print(fr""" ​
""")
print(Rf""" ​
""")

# https://github.com/astral-sh/ruff/issues/18815
b = "\"
sub = "\"
esc = "\"
zwsp = "\​"
nul = "\ "

# tstrings
esc = t'esc esc '
nested_tstrings = t'{t'{t''}'}'
nested_ftstrings = t'{f'{t''}'}'

