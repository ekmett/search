module Data.Search.LazyBool (B(..)) where

-- | Bool with a lazier Ord as suggested <https://www.reddit.com/r/haskell/comments/7arjd1/more_defined_boolean_comparisons/ here>
newtype B = B Bool deriving (Eq,Show,Read)

instance Ord B where
  B False <= _ = True
  B _ <= B y = y
  B False < B y = y
  B _ < _ = False
  B False >= B b = not b
  B _ >= _ = True
  B False > _ = False
  B _ > B b = not b
  min (B False) _ = B False
  min _ b = b
  max (B False) b = b
  max _ _ = B True
