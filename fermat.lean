-- Presentation aimed for March 4, 2020
-- (prime p = 4k+1 is sum of two squares)

-- Must arrive at 10:00, MIT Lab on that day.

-- https://github.com/leanprover-community/mathlib/blob/master/docs/install/windows.md

import tactic
import algebra.group_power
import data.int.basic
--import data.zmod.quadratic_reciprocity
universe u
local attribute [instance] classical.prop_decidable

def ex1 (x y z : ℕ) : ℕ := x + y * z

def even (n : ℕ) : Prop := ∃ k, n = 2*k
def odd (n : ℕ) : Prop := ∃ k, n = 2*k+1

lemma even_or_odd (n : ℕ) : or (even n) (odd n) :=
begin
induction n with d hd,
left,
rw even,
use 0,
simp,
cases hd with p q,
rw even at p,
cases p with k p,
right,
rw odd,
use k,
rw p,
rw odd at q,
cases q with k q,
left,
rw even,
use k+1,
rw mul_add,
rw q,
refl,
end

lemma not_both_even_odd (n : ℕ) : ¬((even n) ∧ (odd n)) :=
begin
by_cases h : (even n) ∧ (odd n),
exfalso,
cases h with h1 h2,
rw even at h1,
cases h1 with k h1k,
rw odd at h2,
cases h2 with k' h2k,
rw h1k at h2k,
have hk := nat.mul_mod_right 2 k,
rw h2k at hk,
rw add_comm at hk,
have hk1 := nat.add_mul_mod_self_left 1 2 k',
have one_lt_two : 1 < 2 := by {exact nat.lt_succ_self 1},
have one_mod_two_is_one := nat.mod_eq_of_lt one_lt_two,
rw one_mod_two_is_one at hk1,
rw hk at hk1,
have zero_lt_one : 0 < 1 := by exact nat.lt_succ_self 0,
rw hk1 at zero_lt_one,
exact lt_irrefl 1 zero_lt_one,
exact h,
end

lemma even_plus_even_is_even (n m : ℕ) (h : and (even n) (even m)) : even (n+m) :=
begin
cases h with p q,
rw even at p,
cases p with k p,
rw even at q,
cases q with l q,
rw even,
use k+l,
rw mul_add,
rw p,
rw q,
end

lemma even_plus_odd_is_odd (n m : ℕ) (h : and (even n) (odd m)) : odd (n+m) :=
begin
cases h with p q,
rw even at p,
cases p with k p,
rw odd at q,
cases q with l q,
rw odd,
use k+l,
rw mul_add,
rw p,
rw q,
ring,
end

lemma odd_plus_even_is_odd (n m : ℕ) (h : and (odd n) (even m)) : odd (n+m) :=
begin
rw and_comm at h,
rw add_comm,
apply even_plus_odd_is_odd,
exact h,
end

lemma odd_plus_odd_is_even (n m : ℕ) (h : and (odd n) (odd m)) : even (n+m) :=
begin
cases h with p q,
rw odd at p,
cases p with k p,
rw odd at q,
cases q with l q,
rw even,
use k+l+1,
rw p,
rw q,
rw mul_add,
rw mul_add,
ring,
end

lemma even_minus_even_is_even (n m : ℕ) (h : (even n) ∧ (even m) ∧ (m ≤ n))
  : even (n - m) :=
begin
cases h with h1 h2,
cases h2 with h3 h4,
have deo := even_or_odd (n-m),
cases deo with deven dodd,
exact deven,
exfalso,
have sum := odd_plus_even_is_odd (n-m) m ⟨dodd, h3⟩,
have claim : n - m + m = n,
have summ := nat.le.dest h4,
cases summ with smd summ',
rw add_comm at summ',
rw (eq.symm summ'),
rw nat.add_sub_cancel,
rw claim at sum,
exact not_both_even_odd n ⟨h1, sum⟩,
end

lemma odd_minus_odd_is_even (n m : ℕ) (h : (odd n) ∧ (odd m) ∧ (m ≤ n))
  : even (n - m) :=
begin
cases h with h1 h2,
cases h2 with h3 h4,
have deo := even_or_odd (n-m),
cases deo with deven dodd,
exact deven,
exfalso,
have sum := odd_plus_odd_is_even (n-m) m ⟨dodd, h3⟩,
have claim : n - m + m = n,
have summ := nat.le.dest h4,
cases summ with smd summ',
rw add_comm at summ',
rw (eq.symm summ'),
rw nat.add_sub_cancel,
rw claim at sum,
exact not_both_even_odd n ⟨sum, h1⟩,
end

lemma even_times_nat_is_even (n m : ℕ) (h : even n) : even (n*m) :=
begin
rw even,
rw even at h,
cases h with p kp,
use m*p,
rw kp,
ring,
end

lemma nat_times_even_is_even (n m : ℕ) (h : even m) : even (n*m) :=
begin
rw mul_comm,
apply even_times_nat_is_even,
exact h,
end

lemma odd_times_odd_is_odd (n m : ℕ) (h : and (odd n) (odd m)) : odd (n*m) :=
begin
rw odd,
cases h with h1 h2,
rw odd at h1,
cases h1 with p kp,
rw odd at h2,
cases h2 with q kq,
use 2*p*q + p + q,
rw kp,
rw kq,
ring,
end

lemma even_square_is_even (n : ℕ) (h : even n) : even (n^2) :=
begin
rw nat.pow_two,
exact nat_times_even_is_even n n h,
end

lemma odd_square_is_odd (n : ℕ) (h : odd n) : odd (n^2) :=
begin
rw nat.pow_two,
exact odd_times_odd_is_odd n n ⟨h, h⟩,
end

lemma not_and_eq_or_not (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
begin
split,
intro f,
 by_cases hp : p,
  { by_cases hq : q,
    { exact (f ⟨hp, hq⟩).elim, },
    exact or.inr hq, },
  { exact or.inl hp, },
intro g,
cases g with g1 g2,
by_cases h : p ∧ q,
exfalso,
cases h with h1 h2,
exact g1(h1),
exact h,
by_cases h : p ∧ q,
exfalso,
cases h with h1 h2,
exact g2(h2),
exact h,
end

lemma not_or_eq_and_not (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
begin
split,
intro f,
by_cases hp : p,
have i := or.intro_left q hp,
exfalso,
exact f(i),
by_cases hq : q,
have i := or.intro_right p hq,
exfalso,
exact f(i),
exact ⟨hp, hq⟩,
intro f,
cases f with f1 f2,
by_cases h : p ∨ q,
cases h with h1 h2,
exfalso,
exact f1(h1),
exfalso,
exact f2(h2),
exact h,
end

lemma pos_or_zero (n : ℕ) : 0 < n ∨ n = 0 :=
begin
have tri := lt_trichotomy 0 n,
cases tri with tri1 tri2,
left,
exact tri1,
cases tri2 with tri3 tri4,
right,
exact (eq.symm tri3),
exfalso,
have nng := zero_le n,
have lt1 := lt_of_le_of_lt nng tri4,
exact lt_irrefl 0 lt1,
end

lemma mul_cancel (a b c : ℕ) (h : a*b = a*c) (p : 0 < a) : b = c :=
begin
have ltr := lt_trichotomy b c,
cases ltr with ltr' ltr1,
exfalso,
have thing := mul_lt_mul_of_pos_left ltr' p,
rw h at thing,
exact lt_irrefl (a*c) thing,
cases ltr1 with ltr2 ltr3,
exact ltr2,
exfalso,
have thing := mul_lt_mul_of_pos_left ltr3 p,
rw h at thing,
exact lt_irrefl (a*c) thing,
end

lemma int_mul_cancel (a b c : ℤ) (h : a*b = a*c) (p : 0 < a) : b = c :=
begin
have ltr := lt_trichotomy b c,
cases ltr with ltr' ltr1,
exfalso,
have thing := mul_lt_mul_of_pos_left ltr' p,
rw h at thing,
exact lt_irrefl (a*c) thing,
cases ltr1 with ltr2 ltr3,
exact ltr2,
exfalso,
have thing := mul_lt_mul_of_pos_left ltr3 p,
rw h at thing,
exact lt_irrefl (a*c) thing,
end

lemma int_mul_cancel_lt (a b c : ℤ) (h : a*b < a*c) (p : 0 < a) : b < c :=
begin
have ltr := lt_trichotomy b c,
cases ltr with ltr' ltr1,
exact ltr',
exfalso,
cases ltr1 with ltr2 ltr3,
rw ltr2 at h,
exact lt_irrefl (a*c) h,
have th := mul_lt_mul_of_pos_left ltr3 p,
exact lt_irrefl (a*b) (lt_trans h th),
end

-- I imagine that those will be important.  Now for the real deal.

def divides (n m : ℕ) : Prop := ∃ k, n*k = m
def prime' (p : ℕ) : Prop := 1 < p ∧ (∀ k, (divides k p → (k = 1 ∨ k = p)))

lemma square_eq_times_itself (a : ℤ) : a^2 = a*a :=
begin
rw pow_succ,
rw pow_succ,
rw pow_zero,
rw mul_one,
end

lemma square_eq_sq_of_nat (a : ℤ) : ∃(n:ℕ),(a^2=(n:ℤ)^2) :=
begin
have ltr := lt_trichotomy 0 a,
cases ltr with ltr1 ltr',
have thing := int.eq_coe_of_zero_le (le_of_lt ltr1),
cases thing with n th',
use n,
rw th',
cases ltr' with ltr2 ltr3,
use 0,
rw (eq.symm ltr2),
ring,
have th := int.add_lt_add_left ltr3 (-a),
rw add_zero at th,
have fill_in_hole : -a+a=0 := by ring,
rw fill_in_hole at th,
have thing := int.eq_coe_of_zero_le (le_of_lt th),
cases thing with n th',
use n,
rw (eq.symm th'),
ring,
end

lemma nonzero_square_pos (a : ℤ) (h : 0 ≠ a) : 0 < a^2 :=
begin
by_cases p : 0 < a,
rw square_eq_times_itself,
rw [←( int.mul_zero a)],
exact mul_lt_mul_of_pos_left p p,
have q := lt_trichotomy 0 a,
cases q,
exfalso,
apply p,
exact q,
cases q,
exfalso,
apply h,
exact q,
rw square_eq_times_itself,
rw [←( int.mul_zero a)],
exact mul_lt_mul_of_neg_left q q,
end

lemma square_nonneg (a : ℤ) : 0 <= a^2 :=
begin
by_cases p : a = 0,
rw p,
refl,
apply le_of_lt,
apply nonzero_square_pos,
by_cases q : 0 = a,
have r := eq.symm q,
exfalso,
apply p,
exact r,
exact q,
end

lemma LCex (a p : ℕ) (hp : 0 < p) :
  ∃(d:ℕ), 0 < d ∧ (∃(x:ℤ), (∃(y:ℤ), (x*a + y*p = d))) :=
begin
use (a*↑a+p*↑p),
split,
have q := square_nonneg(↑a),
rw square_eq_times_itself at q,
have s := nonzero_square_pos(↑p),
norm_cast,
rw square_eq_times_itself at s,
norm_cast at s,
norm_cast at q,
by_cases pz : 0 = p,
rw pz at hp,
have ir := gt_irrefl p,
exfalso,
apply ir,
exact hp,
have r1 := s(pz),
have ala := add_lt_add_left r1 (a*a),
rw add_zero at ala,
exact lt_of_le_of_lt q ala,
norm_cast,
use a,
use p,
norm_cast,
end

lemma div_alg (a b : ℕ) (hp : 0 < b) : ∃(r q : ℕ), (a = b*q+r ∧ r < b) :=
begin
induction a with d hd,
use 0,
use 0,
split,
ring,
exact hp,
cases hd with r rh,
cases rh with q qh,
cases qh with qh1 qh2,
by_cases p : nat.succ r = b,
use 0,
use q+1,
rw qh1,
split,
have p1 := eq.symm p,
rw p1,
ring,
exact hp,
have qh3 := nat.succ_le_of_lt qh2,
have tri := lt_trichotomy (nat.succ r) b,
cases tri with tri1 tri2,
use nat.succ r,
use q,rw qh1,
rw nat.add_succ,
split,
refl,
exact tri1,
cases tri2 with tri3 tri4,
exfalso,
apply p,
exact tri3,
exfalso,
have i := nat.lt_of_le_of_lt qh3 tri4,
have ir := lt_irrefl (nat.succ r),
apply ir,
exact i,
end

lemma div_alg_near_zero (a b : ℕ) (b_pos : 0 < b) (ho : odd b) :
  ∃(q:ℤ), ∃(r:ℤ), ((a:ℤ) = b*q+r ∧ 2*r < b ∧ -2*r < b) :=
begin
have div := div_alg a b b_pos,
cases div with r divr,
cases divr with q divq,
have tri := lt_trichotomy (2*r) b,
cases tri with tri1 tri2,
use q,
use r,
cases divq with divq1 divq2,
split,
norm_cast,
exact divq1,
split,
norm_cast,
exact tri1,
have claim : (-2:ℤ)*r ≤ 0,
have thing := zero_le (2*r),
have thing2 : (0 ≤ 2 * (r : ℤ)) :=
  by { norm_cast, exact thing },
have st := add_le_add_left thing2 ((-2:ℤ)*r),
rw add_zero at st,
have claim1 : (-2:ℤ) * ↑r + 2 * ↑r = 0 := by ring,
rw claim1 at st,
exact st,
have b_pos_int : (0 < (b:ℤ)) := by {norm_cast, exact b_pos},
exact lt_of_le_of_lt claim b_pos_int,
cases tri2 with tri3 tri4,
exfalso,
have claim : even b := by {rw even, use r, exact (eq.symm tri3)},
have not_both := not_both_even_odd b,
exact not_both ⟨claim, ho⟩,
use q+1,
use r-b,
cases divq with divq1 divq2,
split,
rw divq1,
push_cast,
ring,
split,
have claim : 0 < (b:ℤ) := by {norm_cast, exact b_pos},
have claim2 : (r:ℤ) < (b:ℤ) := by {norm_cast, exact divq2},
have st := add_lt_add_left claim2 (-b:ℤ),
have claim3 : -(b:ℤ) + (r:ℤ) = (r:ℤ) - (b:ℤ) := by {ring},
rw claim3 at st,
have fillinhole : -(b:ℤ) + (b:ℤ) = 0 := by {ring},
rw fillinhole at st,
have st' := mul_lt_mul_of_pos_left st (lt_trans zero_lt_one one_lt_two),
rw mul_zero at st',
exact (lt_trans st' claim),
have claim : (b:ℤ) < 2*(r:ℤ) := by {norm_cast, exact tri4},
have st := add_lt_add_left claim (b - 2*(r:ℤ)),
have claim2 : (b:ℤ) - 2*(r:ℤ) + b = (-(2:ℤ))*(r-(b:ℤ)) := by {ring},
rw claim2 at st,
have claim3 : (b:ℤ) - 2*(r:ℤ) + 2*r = b := by {ring},
rw claim3 at st,
exact st,
end

lemma abs_thing (a b : ℤ) (h1 : a < b) (h2 : -a < b) : a^2 < b^2 :=
begin
have h1' := add_lt_add_right h1 (-a),
have f1 : a + (-a) = 0 := by ring,
rw f1 at h1',
have h2' := add_lt_add_right h2 a,
have f2 : (-a) + a = 0 := by ring,
rw f2 at h2',
have thing : 0 < (b+a)*(b+(-a)) := by {exact mul_pos' h2' h1'},
have soandso : (b+a)*(b+(-a)) = b^2-a^2 := by ring,
rw soandso at thing,
have res := add_lt_add_right thing (a^2),
rw zero_add at res,
have th' : b^2-a^2+a^2 = b^2 := by ring,
rw th' at res,
exact res,
end

def isLC (a p d : ℕ) : Prop := 0 < d ∧ (∃(x:ℤ), (∃(y:ℤ), (x*a + y*p = d)))

-- The following lemmas show that the *smallest* positive integer linear
-- combination of a and b is a common divisor of a and b.

lemma bezout (a b d : ℕ) (h_pos : 0 < d)
  (h1 : ∃(x:ℤ), (∃(y:ℤ), (x*a + y*b = d)))
  (h2 : ∀(d':ℕ), (0 < d' ∧ ∃(x:ℤ), (∃(y:ℤ), (x*a + y*b = d'))) → d ≤ d') :
  divides d a :=
begin
have r1 := div_alg a d h_pos,
cases r1 with r hr,
cases hr with q hq,
cases hq with hq1 hq2,
have htr := pos_or_zero r,
cases htr with htr1 htr2,
exfalso,
have claim1 : (a:ℤ)-d*q = r,
rw hq1,
push_cast,
ring,
cases h1 with x_ex hx,
cases hx with y_ex hy,
have claim2 : (1-x_ex*q)*a + (-y_ex*q)*b = r,
rw (eq.symm claim1),
rw (eq.symm hy),
ring,
have thing := h2(r),
have EG : ∃ (x y : ℤ), x * ↑a + y * ↑b = ↑r,
use (1 - x_ex * q),
use (-y_ex * q),
exact claim2,
have concl := thing(⟨htr1, EG⟩),
have ir1 := lt_of_le_of_lt concl hq2,
have ir2 := lt_irrefl d,
exact ir2(ir1),
rw htr2 at hq1,
rw add_zero at hq1,
rw divides,
use q,
rw hq1,
end

-- The above shows that d divides a.
-- Now we apply it to show d divides both of them, without
-- rewriting the entire argument.

lemma bezout_doub (a b d : ℕ) (h_pos : 0 < d)
  (h1 : ∃(x:ℤ), (∃(y:ℤ), (x*a + y*b = d)))
  (h2 : ∀(d':ℕ), (0 < d' ∧ ∃(x:ℤ), (∃(y:ℤ), (x*a + y*b = d'))) → d ≤ d') :
  divides d a ∧ divides d b :=
begin
split,
exact bezout a b d h_pos h1 h2,
have h1_swap : ∃ (x y : ℤ), x * b + y * a = d,
cases h1 with xex h1a,
cases h1a with yex h1b,
use yex,
use xex,
rw (eq.symm h1b),
rw add_comm,
have h2_swap : ∀ (d' : ℕ), (0 < d' ∧ ∃ (x y : ℤ), x * b + y * a = d') → d ≤ d',
intro d',
intro f,
cases f with f1 f2,
have f2_swap : ∃ (x y : ℤ), x * a + y * b = d',
cases f2 with xex f2a,
cases f2a with yex f2b,
use yex,
use xex,
rw (eq.symm f2b),
rw add_comm,
have thing := h2(d'),
exact thing(⟨f1, f2_swap⟩),
exact bezout b a d h_pos h1_swap h2_swap,
end

lemma bezout1 (a p : ℕ) (hp : prime' p) (ha : ¬(divides p a)) :
  ∃(x:ℤ), (∃(y:ℤ), (x*a + y*p = 1)) :=
begin
rw prime' at hp,
cases hp with hp1 hp2,
have zero_lt_one := nat.lt_succ_self 0,
have p_pos := lt_trans zero_lt_one hp1,
have dh : ∃ (d : ℕ), 0 < d ∧ ∃ (x y : ℤ), x * ↑a + y * ↑p = ↑d := LCex a p p_pos,
let d := nat.find(dh),
have dx : 0 < d ∧ ∃ (x y : ℤ), x * ↑a + y * ↑p = ↑d := nat.find_spec dh,
have dm : ∀ d', (0 < d' ∧ ∃ (x y : ℤ), x * ↑a + y * ↑p = ↑d') → d ≤ d' := λ d', nat.find_min' dh,
cases dx with d_pos dx2,
have dividing := bezout_doub a p d d_pos dx2 dm,
cases dividing with div1 div2,
have concl := hp2(d)(div2),
cases concl with c1 c2,
cases dx2 with xex dx3,
cases dx3 with yex dx4,
use xex,
use yex,
rw c1 at dx4,
norm_cast at dx4,
exact dx4,
exfalso,
rw c2 at div1,
exact ha(div1),
end

lemma neg_one_is_square (p : ℕ) (hp : prime' p) (hm : divides 4 (p-1)) :
  ∃ x, (0 < x ∧ x < p ∧ divides p (x^2+1)) :=
begin
sorry -- when I tried to import quadratic_reciprocity, memory was overloaded
end

lemma nat_square_sep (a b : ℕ) (a_pos : 0 < a) (bound : a < b) : a^2 + 1 < b^2 :=
begin
have b_pos := lt_trans a_pos bound,
have st1 := nat.mul_lt_mul_of_pos_right bound b_pos,
have st2 := nat.mul_lt_mul_of_pos_left bound a_pos,
have st2' := nat.succ_le_of_lt st2,
have res := lt_of_le_of_lt st2' st1,
rw nat.pow_two,
rw nat.pow_two,
exact res,
end

theorem mult_sum_of_two_squares (p : ℕ) (hp : prime' p) (hm : divides 4 (p-1)) :
  ∃ m, (0 < m ∧ m < p ∧ ∃ x, ∃ y, m*p = x^2+y^2) :=
begin
have q := neg_one_is_square p hp hm,
cases q with a ka,
rw divides at ka,
cases ka with a_pos ka1,
cases ka1 with a_bound ka2,
cases ka2 with n kb,
use n,
split,
have zero_lt_one := nat.lt_succ_self 0,
have posmul := nat.mul_lt_mul_of_pos_left a_pos a_pos,
rw mul_zero at posmul,
have summing := add_lt_add_right posmul 1,
rw zero_add at summing,
have res := lt_trans zero_lt_one summing,
rw nat.pow_two at kb,
rw (eq.symm kb) at res,
have n_pos_zero := pos_or_zero n,
cases n_pos_zero with n_pos n_zero,
exact n_pos,
exfalso,
rw n_zero at res,
rw mul_zero at res,
exact lt_irrefl 0 res,
split,
have st := nat_square_sep a p a_pos a_bound,
rw (eq.symm kb) at st,
rw nat.pow_two at st,
have tri := lt_trichotomy p n,
cases tri with tri1 tri2,
exfalso,
have tri1a := nat.mul_lt_mul_of_pos_left tri1 (lt.trans a_pos a_bound),
have tri1b := lt.trans st tri1a,
exact lt_irrefl (p*n) tri1b,
cases tri2 with tri3 tri4,
exfalso,
rw tri3 at st,
exact lt_irrefl (n*n) st,
exact tri4,
use a,
use 1,
rw mul_comm,
rw kb,
ring,
end

lemma prelim (x y : ℕ) (h : x < y) :
  2 * (x ^ 2 + y ^ 2) = (y + x) ^ 2 + (y - x) ^ 2 :=
begin
apply int.coe_nat_inj,
push_cast,
rw int.coe_nat_sub (le_of_lt h),
ring,
simp,
end

lemma halving_first (n x y : ℕ) (h : x < y) (h1 : 2*n = x^2 + y^2) :
  ∃a:ℕ, ∃b:ℕ, n = a^2 + b^2 :=
begin
have zero_lt_two := lt_trans (nat.lt_succ_self 0) (nat.lt_succ_self 1),
have xeo := even_or_odd x,
have yeo := even_or_odd y,
cases xeo with x_even x_odd,
cases yeo with y_even y_odd,
have sum_even := even_plus_even_is_even y x ⟨y_even, x_even⟩,
have diff_even := even_minus_even_is_even y x ⟨y_even, x_even, le_of_lt h⟩,
rw even at sum_even,
cases sum_even with sum' sum_ev,
rw even at diff_even,
cases diff_even with diff' diff_ev,
use sum',
use diff',
have claim : 2*n = 2*(sum'^2 + diff'^2),
rw h1,
have claim' : 2*(x^2+y^2) = 4*(sum'^2+diff'^2),
have thing : 4*(sum'^2+diff'^2) = (2*sum')^2+(2*diff')^2 := by ring,
rw thing,
rw (eq.symm sum_ev),
rw (eq.symm diff_ev),
exact prelim x y h,
have thing : 4*(sum'^2+diff'^2) = 2*(2*(sum'^2+diff'^2)) := by ring,
rw thing at claim',
exact mul_cancel 2 (x^2+y^2) (2*(sum'^2+diff'^2)) claim' zero_lt_two,
exact mul_cancel 2 n (sum'^2+diff'^2) claim zero_lt_two,

exfalso,
have xsq_even := even_times_nat_is_even x x x_even,
have ysq_odd := odd_times_odd_is_odd y y ⟨y_odd, y_odd⟩,
have sum_odd := even_plus_odd_is_odd (x*x) (y*y) ⟨xsq_even, ysq_odd⟩,
rw nat.pow_two at h1,
rw nat.pow_two at h1,
have claim : even (x*x+y*y) := by {rw even, use n, rw h1},
exact not_both_even_odd (x*x+y*y) ⟨claim, sum_odd⟩,
cases yeo with y_even y_odd,

exfalso,
have xsq_odd := odd_times_odd_is_odd x x ⟨x_odd, x_odd⟩,
have ysq_even := even_times_nat_is_even y y y_even,
have sum_odd := odd_plus_even_is_odd (x*x) (y*y) ⟨xsq_odd, ysq_even⟩,
rw nat.pow_two at h1,
rw nat.pow_two at h1,
have claim : even (x*x+y*y) := by {rw even, use n, rw h1},
exact not_both_even_odd (x*x+y*y) ⟨claim, sum_odd⟩,

have sum_even := odd_plus_odd_is_even y x ⟨y_odd, x_odd⟩,
have diff_even := odd_minus_odd_is_even y x ⟨y_odd, x_odd, le_of_lt h⟩,
rw even at sum_even,
cases sum_even with sum' sum_ev,
rw even at diff_even,
cases diff_even with diff' diff_ev,
use sum',
use diff',
have claim : 2*n = 2*(sum'^2 + diff'^2),
rw h1,
have claim' : 2*(x^2+y^2) = 4*(sum'^2+diff'^2),
have thing : 4*(sum'^2+diff'^2) = (2*sum')^2+(2*diff')^2 := by ring,
rw thing,
rw (eq.symm sum_ev),
rw (eq.symm diff_ev),
exact prelim x y h,
have thing : 4*(sum'^2+diff'^2) = 2*(2*(sum'^2+diff'^2)) := by ring,
rw thing at claim',
exact mul_cancel 2 (x^2+y^2) (2*(sum'^2+diff'^2)) claim' zero_lt_two,
exact mul_cancel 2 n (sum'^2+diff'^2) claim zero_lt_two,
end

-- halving just applies halving_first several times to rid the assumption
-- of the comparison on x and y.

lemma halving (n x y : ℕ) (h1 : 2*n = x^2 + y^2) :
  ∃a:ℕ, ∃b:ℕ, n = a^2 + b^2 :=
begin
have ltr := lt_trichotomy x y,
cases ltr with ltr' ltr1,
exact halving_first n x y ltr' h1,
cases ltr1 with ltr2 ltr3,
use x,
use 0,
rw (eq.symm ltr2) at h1,
have claim : x^2 + x^2 = 2*(x^2) := by ring,
rw claim at h1,
have zero_lt_two := lt_trans (nat.lt_succ_self 0) (nat.lt_succ_self 1),
have thing := mul_cancel 2 n (x^2) h1 zero_lt_two,
rw thing,
ring,
rw add_comm at h1,
exact halving_first n y x ltr3 h1,
end

lemma ineq's (n k : ℕ) (h1 : 0 < 2*n) (h2 : 2*n < k) :
  0 < n ∧ n < k :=
begin
split,
have pz := pos_or_zero n,
cases pz with pz1 pz2,
exact pz1,
exfalso,
rw pz2 at h1,
rw mul_zero at h1,
exact lt_irrefl 0 h1,
have ltr := lt_trichotomy n k,
cases ltr with ltr' ltr1,
exact ltr',
exfalso,
cases ltr1 with ltr2 ltr3,
rw ltr2 at h2,
have claim : k ≤ 2*k,
have thing := add_le_add_left (zero_le k) k,
rw add_zero at thing,
have thing' : k + k = 2*k := by ring,
rw thing' at thing,
exact thing,
have thing := lt_of_le_of_lt claim h2,
exact lt_irrefl k thing,
have zero_lt_two : 0 < 2 := by {
  exact lt_trans (nat.lt_succ_self 0) (nat.lt_succ_self 1)
},
have thing := mul_lt_mul_of_pos_left ltr3 zero_lt_two,
have h2' := lt_trans thing h2,
have claim : k ≤ 2*k,
have thing := add_le_add_left (zero_le k) k,
rw add_zero at thing,
have thing' : k + k = 2*k := by ring,
rw thing' at thing,
exact thing,
have thing := lt_of_le_of_lt claim h2',
exact lt_irrefl k thing,
end

theorem sum_of_two_squares (p : ℕ) (hp : prime' p) (hm : divides 4 (p-1)) :
  ∃ x, ∃ y, p = x^2+y^2 :=
begin
let m := nat.find(mult_sum_of_two_squares p hp hm),
have mx : 0 < m ∧ m < p ∧ ∃ x, ∃ y, m*p = x^2+y^2 := nat.find_spec(mult_sum_of_two_squares p hp hm),
have mm : ∀ m', (0 < m' ∧ m' < p ∧ ∃ x, ∃ y, m'*p = x^2+y^2) → m ≤ m' := λ d', nat.find_min'(mult_sum_of_two_squares p hp hm),
have meo := even_or_odd m,
cases mx with mx1 mx1',
cases mx1' with mx2 mx3,
cases meo with m_even m_odd,
exfalso,
rw even at m_even,
cases m_even with m' m_ev,
cases mx3 with xex mx3',
cases mx3' with yex mx4,

rw m_ev at mx4,
rw mul_assoc at mx4,
have half := halving (m'*p) xex yex mx4,
rw m_ev at mx1,
rw m_ev at mx2,
have ineqs := ineq's m' p mx1 mx2,
cases ineqs with ineq1 ineq2,
have fact := mm m' ⟨ineq1, ineq2, half⟩,
rw m_ev at fact,
have fact2 := add_lt_add_left ineq1 m',
rw add_zero at fact2,
have ir := lt_of_le_of_lt fact fact2,
have claim : m' + m' = 2 * m' := by ring,
rw claim at ir,
exact lt_irrefl (2*m') ir,

-- Now for the case that m is odd.

by_cases is_m_one : m = 1,
rw is_m_one at mx3,
cases mx3 with xex mx3',
cases mx3' with yex mx3'',
rw one_mul at mx3'',
use xex,
use yex,
exact mx3'',

-- Now for the case that m is odd and > 1.

cases mx3 with xex mx3',
cases mx3' with yex mx4,
have xd := div_alg_near_zero xex m mx1 m_odd,
cases xd with qx xd'',
cases xd'' with x1 xd',
have yd := div_alg_near_zero yex m mx1 m_odd,
cases yd with qy yd'',
cases yd'' with y1 yd',
cases xd' with xd1 xd1',
cases xd1' with xd2 xd3,
cases yd' with yd1 yd1',
cases yd1' with yd2 yd3,

have claim : ∃(n:ℤ), (m:ℤ)*n = x1^2+y1^2,
use (p:ℤ) - (xex+x1)*qx - (yex+y1)*qy,
have thing0 : ↑m * (↑p - (↑xex + x1) * qx - (↑yex + y1) * qy)
  = (↑m * ↑p) - ↑m * (↑xex + x1) * qx - ↑m * (↑yex + y1) * qy := by ring,
rw thing0,
have thing0' : (m:ℤ)*p = (xex:ℤ)^2+yex^2 := by {norm_cast, exact mx4},
have thing1 : x1 = (xex:ℤ) - (m:ℤ)*qx := by {rw xd1, ring},
have thing2 : y1 = (yex:ℤ) - (m:ℤ)*qy := by {rw yd1, ring},
rw thing1,
rw thing2,
rw thing0',
ring,

cases claim with n cn,

have n_pos : 0 < n,
have ltr := lt_trichotomy 0 n,
cases ltr with ltr1 ltr1',
exact ltr1,
exfalso,
cases ltr1' with ltr2 ltr3,
rw (eq.symm ltr2) at cn,
rw mul_zero at cn,
have x1sq_nn := square_nonneg x1,
have y1sq_nn := square_nonneg y1,
have clema := add_le_add_right x1sq_nn (y1^2),
rw zero_add at clema,
rw (eq.symm cn) at clema,
have y1sq_zero := le_antisymm clema y1sq_nn,
have y1_zero : 0 = y1 := by {
  by_cases contr : 0 = y1,
  exact contr,
  exfalso,
  have thing := nonzero_square_pos y1 contr,
  rw y1sq_zero at thing,
  exact lt_irrefl 0 thing
},
have clema' := add_le_add_left y1sq_nn (x1^2),
rw add_zero at clema',
rw (eq.symm cn) at clema',
have x1sq_zero := le_antisymm clema' x1sq_nn,
have x1_zero : 0 = x1 := by {
  by_cases contr : 0 = x1,
  exact contr,
  exfalso,
  have thing := nonzero_square_pos x1 contr,
  rw x1sq_zero at thing,
  exact lt_irrefl 0 thing
},
rw (eq.symm x1_zero) at xd1,
rw add_zero at xd1,
rw (eq.symm y1_zero) at yd1,
rw add_zero at yd1,
have mx4' : (m:ℤ)*p = (xex:ℤ)^2 + yex^2 := by {norm_cast, exact mx4},
rw xd1 at mx4',
rw yd1 at mx4',
have mx4'' : (m:ℤ)*p = (m:ℤ)*(m*(qx^2+qy^2)) := by {rw mx4', ring},
have int_m_pos : (0:ℤ) < (m:ℤ) := by {norm_cast, exact mx1},
have thing := int_mul_cancel m p (m*(qx^2+qy^2)) mx4'' int_m_pos,
have qx_nat := square_eq_sq_of_nat qx,
cases qx_nat with qxn qx_nat',
have qy_nat := square_eq_sq_of_nat qy,
cases qy_nat with qyn qy_nat',
rw qx_nat' at thing,
rw qy_nat' at thing,
have thing' := int.coe_nat_inj thing,
have oth : divides m p := by {
  rw divides, use qxn * (qxn * 1) + qyn * (qyn * 1), exact eq.symm thing'},
rw prime' at hp,
cases hp with hp1 hp2,
have conc := hp2 m oth,
cases conc with conc1 conc2,
exact is_m_one conc1,
rw conc2 at mx2,
exact lt_irrefl p mx2,
-- FINALLY confirmed n can't be zero.
have x1sq_nn := square_nonneg x1,
have y1sq_nn := square_nonneg y1,
have clema := add_le_add_right x1sq_nn (y1^2),
rw zero_add at clema,
rw (eq.symm cn) at clema,
have clema' := le_trans y1sq_nn clema,
have mx1' : (m:ℤ) > 0 := by {norm_cast, exact mx1},
have thing := linarith.mul_neg ltr3 mx1',
exact lt_irrefl 0 (lt_of_le_of_lt clema' thing),

have n_lt_m : n < m,
have two_squared_is_four : (2:ℤ)^2 = (4:ℤ) := by ring,
have negstx : (-2)*x1=-(2*x1) := by ring,
rw negstx at xd3,
have squarerelx := abs_thing (2*x1) (m:ℤ) xd2 xd3,
rw mul_pow at squarerelx,
rw two_squared_is_four at squarerelx,
have negsty : (-2)*y1=-(2*y1) := by ring,
rw negsty at yd3,
have squarerely := abs_thing (2*y1) (m:ℤ) yd2 yd3,
rw mul_pow at squarerely,
rw two_squared_is_four at squarerely,
have cn'4 : 4*((m:ℤ)*n) = 4*(x1^2+y1^2) := by {rw cn},
rw mul_add at cn'4,
have compare := add_lt_add squarerelx squarerely,
rw (eq.symm cn'4) at compare,
have th'1 : 4*((m:ℤ)*n)=(2*(m:ℤ))*(2*n) := by ring,
rw th'1 at compare,
have th'2 : (m:ℤ)^2+m^2 = (2*(m:ℤ))*m := by ring,
rw th'2 at compare,
have thong : 0 < 2*(m:ℤ) := by {
  norm_cast,
  have mx1' := add_lt_add_left mx1 m,
  rw add_zero at mx1',
  have th : 2*m=m+m := by ring,
  rw th,
  exact (lt_trans mx1 mx1')
},
have res := int_mul_cancel_lt (2*(m:ℤ)) (2*n) (m:ℤ) compare thong,
have final : n < 2*n := by {
  have fin := add_lt_add_left n_pos n,
  rw add_zero at fin,
  have th : 2*n=n+n := by ring,
  rw th, exact fin
},
exact lt_trans final res,

-- Now we can finally carry on with the rest.
-- We just need to show n*p is a sum of two squares.
have first_divis_lemma : ∃(a:ℤ),(m:ℤ)*a=xex*x1+yex*y1,
use p - xex*qx - yex*qy,
have claim : (m:ℤ)*(p-xex*qx-yex*qy) = (m:ℤ)*p - (m:ℤ)*(xex*qx+yex*qy) := by ring,
rw claim,
have mx4' : ((m:ℤ)*p = (xex:ℤ)^2+yex^2) := by {norm_cast, exact mx4},
rw mx4',
have xd1' : x1 = (xex:ℤ)-((m:ℤ)*qx) := by {rw xd1, ring},
rw xd1',
have yd1' : y1 = (yex:ℤ)-((m:ℤ)*qy) := by {rw yd1, ring},
rw yd1',
ring,

have second_divis_lemma : ∃(b:ℤ),(m:ℤ)*b=xex*y1-yex*x1,
use (yex:ℤ)*qx - (xex:ℤ)*qy,
have xd1' : x1 = (xex:ℤ)-((m:ℤ)*qx) := by {rw xd1, ring},
rw xd1',
have yd1' : y1 = (yex:ℤ)-((m:ℤ)*qy) := by {rw yd1, ring},
rw yd1',
ring,

cases first_divis_lemma with a fdl,
cases second_divis_lemma with b sdl,
have claim1 : ((m:ℤ)^2)*(n*p) = (xex*x1+yex*y1)^2 + (xex*y1-yex*x1)^2 := by {
  have thong : ((m:ℤ)^2)*(n*p) = ((m:ℤ)*n)*((m:ℤ)*p) := by ring,
  rw thong,
  have mx4' : ((m:ℤ)*p = (xex:ℤ)^2+yex^2) := by {norm_cast, exact mx4},
  rw cn,
  rw mx4',
  ring
},
rw (eq.symm fdl) at claim1,
rw (eq.symm sdl) at claim1,
have dist : ((m:ℤ)*a)^2 + ((m:ℤ)*b)^2 = (m:ℤ)^2*(a^2+b^2) := by ring,
rw dist at claim1,
have mx1' : 0 < (m:ℤ) := by {norm_cast, exact mx1},
by_cases could_it_be : (0:ℤ) = (m:ℤ),
exfalso,
rw could_it_be at mx1',
exact lt_irrefl (m:ℤ) mx1',
have sq_pos := nonzero_square_pos (m:ℤ) could_it_be,
have res := int_mul_cancel ((m:ℤ)^2) (n*(p:ℤ)) (a^2+b^2) claim1 sq_pos,
have n_can_be_coed := int.eq_coe_of_zero_le (le_of_lt n_pos),
cases n_can_be_coed with n' nc,
have ext_claim : ∃ (x y : ℕ), n'*p = x^2+y^2 := by {
  have a_nat := square_eq_sq_of_nat a,
  cases a_nat with aex a_n,
  have b_nat := square_eq_sq_of_nat b,
  cases b_nat with bex b_n,
  use aex, use bex,
  apply int.coe_nat_inj,
  push_cast,
  rw (eq.symm a_n),
  rw (eq.symm b_n),
  rw (eq.symm nc), exact res
},
rw nc at n_pos,
have n_pos' := int.coe_nat_lt.mp n_pos,
rw nc at n_lt_m,
have n_lt_m' := int.coe_nat_lt.mp n_lt_m,
have n_lt_p := lt_trans n_lt_m' mx2,
have final_thing := mm n' ⟨n_pos', n_lt_p, ext_claim⟩,
exfalso,
exact lt_irrefl m (lt_of_le_of_lt final_thing n_lt_m'),

end