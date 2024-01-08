data Op a x : Set where
  op : (x → a) → Op a x
