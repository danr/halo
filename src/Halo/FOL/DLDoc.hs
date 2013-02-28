module Halo.FOL.DLDoc where

import qualified Data.DList as DL

type DLDoc = DL.DList Char

-- Utilities

cat :: [DLDoc] -> DLDoc
cat = DL.concat

char :: Char -> DLDoc
char = DL.singleton

text :: String -> DLDoc
text = DL.fromList

vcat :: [DLDoc] -> DLDoc
vcat = cat . punctuate newline

hang :: DLDoc -> Int -> [DLDoc] -> DLDoc
hang u i us = vcat (u:map (DL.replicate i ' ' <>) us)

(<>) :: DLDoc -> DLDoc -> DLDoc
(<>) = DL.append

(<+>) :: DLDoc -> DLDoc -> DLDoc
u <+> v = u <> space <> v

punctuate :: DLDoc -> [DLDoc] -> [DLDoc]
punctuate _ []     = []
punctuate p (x:xs) = go x xs
  where
    go d []     = [d]
    go d (e:es) = (d <> p) : go e es

csv :: [DLDoc] -> DLDoc
csv = cat . punctuate comma

newline :: DLDoc
newline = char '\n'

equals :: DLDoc
equals = char '='

unequals :: DLDoc
unequals = text "!="

ampersand :: DLDoc
ampersand = char '&'

pipe :: DLDoc
pipe = char '|'

tilde :: DLDoc
tilde = char '~'

bang :: DLDoc
bang = char '!'

questmark :: DLDoc
questmark = char '?'

colon :: DLDoc
colon = char ':'

comma :: DLDoc
comma = char ','

dot :: DLDoc
dot = char '.'

space :: DLDoc
space = char ' '

darrow :: DLDoc
darrow = text "=>"

arrow :: DLDoc
arrow = text "->"

empty :: DLDoc
empty = DL.empty

parens :: DLDoc -> DLDoc
parens x = '(' `DL.cons` (x `DL.snoc` ')')

brackets :: DLDoc -> DLDoc
brackets x = '[' `DL.cons` (x `DL.snoc` ']')
