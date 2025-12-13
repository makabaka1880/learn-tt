example (a b c : Prop) (x : (b -> c) -> c) : (a -> c) -> (b -> a) -> c :=
  λ u : a -> c => λ v : b -> a => x (λ y : b => u (v y))

theorem t (α β γ : Prop) (x : (γ -> β) -> α -> γ) : (α -> β -> γ) :=
  λ u => λ v => x (λ _ => v) u

#print t
