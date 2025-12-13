example (a b c : Prop) (x : (b -> c) -> c) : (a -> c) -> (b -> a) -> c :=
  λ u : a -> c => λ v : b -> a => x (λ y : b => u (v y))
