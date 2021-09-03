import data.list.basic

namespace list

lemma take_append_sub {α : Type*} (n : ℕ) (l m : list α) :
  take n (l ++ m) = take n l ++ take (n - l.length) m :=
begin
  cases (le_total l.length n),
  calc take n (l ++ m)
      = take (l.length + (n - l.length)) (l ++ m) : by rw nat.add_sub_of_le h
  ... = l ++ take (n - l.length) m                : by rw take_append
  ... = take n l ++ take (n - l.length) m         : by rw take_all_of_le h,

  calc take n (l ++ m) = take n l         : take_append_of_le_length h
  ... = take n l ++ []                    : by rw append_nil
  ... = take n l ++ take 0 m              : rfl
  ... = take n l ++ take (n - l.length) m : by rw nat.sub_eq_zero_of_le h
end

lemma drop_append_sub {α : Type*} (n : ℕ) (l m : list α) :
  drop n (l ++ m) = drop n l ++ drop (n - l.length) m :=
begin
  cases (le_total l.length n),
  calc drop n (l ++ m)
      = drop (l.length + (n - l.length)) (l ++ m) : by rw nat.add_sub_of_le h
  ... = drop (n - l.length) m                     : by rw drop_append
  ... = [] ++ drop (n - l.length) m               : rfl
  ... = drop n l ++ drop (n - l.length) m         : by rw drop_eq_nil_of_le h,

  calc drop n (l ++ m)
      = drop n l ++ m                     : drop_append_of_le_length h
  ... = drop n l ++ drop 0 m              : rfl
  ... = drop n l ++ drop (n - l.length) m : by rw nat.sub_eq_zero_of_le h
end

def ind_app {α : Type*} {motive : list α → Sort*} (h : motive nil)
  (ih : Π (a : α) (l : list α), motive l → motive (l ++ [a])) (l : list α) :
  motive l :=
begin
  rw ←reverse_reverse l,
  induction l.reverse with x l hl,
  exact h,
  rw reverse_cons, exact ih x l.reverse hl
end

end list