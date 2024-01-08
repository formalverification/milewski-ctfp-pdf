instance
  repStream : Representable Stream
  repStream .Repf = ℕ
  repStream .tabulate f = Cons (f 0) (tabulate (f ∘ (_+ 1)))
  repStream .index (Cons b bs) n = if (n == 0) then b else index bs (n - 1)
