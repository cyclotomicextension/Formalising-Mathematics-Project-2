/-
This file is part of the second project based on Ideals in Lean for the Formalising Mathematics 
course at Imperial College London.

Motivation: Ideals form a Complete Lattice. 

Author: Additi Pandey
CID : 02119403
-/

import tactic 

import data.set_like.basic
 
/-!
Defining Ideals in Lean and representing them in the form of a Complete Lattice.
We will start off by defining the ideals in Lean in the form of a structure called `my_ideal`.

## Give the definition of an ideal of a ring.
A subring `A` of a ring `R` is called a (two-sided) ideal of `R` if for every `r ∈ R` and every 
`a ∈ A` both ` r * a` and `a * r` are in `A`.

We will deal with ideals of a commutative ring, which will be denoted by `R`.

To define the ideal of a commutative ring `R`, we will apply the Ideal Test. 
The ideal test says an ideal `A` is a nonempty subset (always has the 0 element) of a ring `R` if 
1. `r * a` in `A` whenever `a ∈ A` and `r ∈ R`. (The ring `R` is commuatative.)
2. `a-b ∈ A` whenever `a, b ∈ A`.

## Implementation notes
Ideal inclusion is denoted by `≤` rather than by `⊆`.
-/

-- Throughout this file, `R` will denote a commutative ring, whose ideals will be talked about. 
variable {R: Type*}

/-- Using the ideal test (mentioned above), the structure `my_ideal` is defined as: -/
structure my_ideal (R : Type*) [comm_ring R] :=
(carrier : set R)
(zero_mem' : (0 : R) ∈ carrier) -- denotes the property of a non-empty subset 
(mul_mem' {a b} : b ∈ carrier → a * b ∈ carrier) -- denotes property 1.
(sub_mem' {a b} : a ∈ carrier → b ∈ carrier → a - b ∈ carrier) -- denotes property 2.

-- Moving to the section of `comm_ring` so as to limit the scope of the variables declared.
section comm_ring

namespace my_ideal

/-
 Declaring variables such that, throughout the code: 
`R` is `comm_ring`
`S, I , J` will denote `my_ideal R`
`a,b` will denote `R`
-/
variables [comm_ring R] (S : my_ideal R) {a b : R} {I J : my_ideal R}

/-- Declaring the instance `set_like` from `my_ideal R` to the set `R` -/
instance : set_like (my_ideal R) R :=
begin
  constructor,
  swap, 
  exact my_ideal.carrier,
  intros p q h,
  cases p,
  cases q,
  congr',
end

-- Checking if inclusion is defined by `set_like`:
#check I ≤ J

/- 
Note: `set_like` defines an instance called `partial_order A` which is followed by a lemma 
which talks about the inclusion of two variables that denote `A`, given by:

lemma le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T := iff.rfl

Hence, the command `#check I ≤ J` right after the declaration of the `set_like` instance. 

However, I have tried showing inclusion more explicitly below:
-/

/--
The lemma given by `mem_carrier`, `mem_mk` and `coe_set_mk`, do not come into use, however, have
still been included in the code as they give some important results.
-/
-- To show: `x ∈ I.carrier` iff `x ∈ I`.
lemma mem_carrier {I : my_ideal R} {x : R} : x ∈ I.carrier ↔ x ∈ I := iff.rfl

-- To show: If `x` fulfills all axioms in `my_ideal R` then `x` is in `set R`.
lemma mem_mk {s : set R} {x : R} (h_one) (h_mul) (h_add) : x ∈ mk s h_one h_mul h_add ↔ x ∈ s := iff.rfl

-- Generalising the previous lemma:
lemma coe_set_mk {s : set R} (h_one) (h_mul) (h_add): (mk s h_one h_mul h_add : set R) = s := rfl

-- Finally, proving inclusion in ideals:
/-- The lemma stating the inclusion of two ideals: -/
lemma mk_le_mk { I J : set R} (h_one) (h_mul) (h_sub) (h_one') (h_mul') (h_sub') :
  mk I h_one h_mul h_sub ≤ mk J h_one' h_mul' h_sub'↔ I ⊆ J := iff.rfl

/-- Two ideals are equal if they have the same elements. -/
theorem ext {I J : my_ideal R}
(h : ∀ x, x ∈ I ↔ x ∈ J) : I = J := set_like.ext h

-- To fix definitional equalities:
/-- Copying an ideal replacing `carrier` with a set that is equal to it: -/
def copy (S : my_ideal R) (s : set R) (hs : s = S) : my_ideal R :=
{ carrier := s,
  zero_mem' := hs.symm ▸ S.zero_mem',
  mul_mem' := hs.symm ▸ S.mul_mem',
  sub_mem' := hs.symm ▸ S.sub_mem',
  }

@[simp] lemma coe_copy (p : my_ideal R) (s : set R) (hs : s = ↑p) :
  (p.copy s hs : set R) = s := rfl

lemma copy_eq (p : my_ideal R) (s : set R) (hs : s = ↑p) : p.copy s hs = p :=
set_like.coe_injective hs

variable (S) 

/-- Every ideal has a zero element. -/
@[simp]theorem zero_mem : (0 : R) ∈ S := S.zero_mem'

/-- Ideals are closed under multiplication. -/
@[simp]theorem mul_mem {x y : R} : y ∈ S → x * y ∈ S := mul_mem' S

/-- Ideals have additive inverses in them. -/
theorem neg_one_mul_mem : b ∈ S → (-1 : R) * b ∈ S := 
begin
  apply mul_mem,
end

/-- Ideals are subsets such that they fulfill  `sub_mem` as they are also additive subgroups. -/
@[simp]theorem sub_mem {x y : R} : x ∈ S → y ∈ S → x - y ∈ S := sub_mem' S

/-
Although, the lemma included in these comments is not used anywhere in the file, it provided me an 
insight as to how to go about proving `add_mem` by using only the available axioms defined in the
structure `my_ideal R`.

theorem neg_one_mul (x ∈ S) : (-1 : R) * x = -x := 
begin
  rw neg_one_mul,
end
-/

/-- Proving that ideals contain additive inverse of their elements with the help of 
the theorem `neg_one_mul_mem`. -/
@[simp] lemma neg_mem : a ∈ S → -a ∈ S := 
begin
  intro h,
  rw neg_eq_neg_one_mul,
  apply neg_one_mul_mem,
  apply h,
end

/-- Ideals are closed under addition. -/
@[simp]theorem add_mem {x y : R} : x ∈ S → y ∈ S → x + y ∈ S := 
begin
  intros h p,
  have hQ: -y ∈ S,
  apply neg_mem,
  exact p,
  have hT : x - (-y) ∈ S,
  apply sub_mem,
  exact h,
  exact hQ,
  finish,
end

/-- Ideals are closed under right multiplication , that is, `a * r ∈ S` 
if `a ∈ S` and `r ∈ R` -/
@[simp]theorem mul_mem_right {x y : R} : x ∈ S → x * y ∈ S := 
begin
  intro h,
  rw mul_comm,
  apply mul_mem,
  exact h,
end

/-- The ideal `(0)` of the commutative ring `R`. -/
instance : has_bot (my_ideal R) :=
⟨{ carrier := {0},
   zero_mem' := set.mem_singleton 0,
   mul_mem' := 
   begin
     intros a b ha,
    simp only[set.mem_singleton_iff] at *,
    rw ha,
    apply mul_zero,
   end,
   sub_mem' := 
   begin
     intros a b ha hb,
     simp only[set.mem_singleton_iff] at *,
     rw ha,
     rw hb,
     simp,
   end
}⟩

/-- The ideal `R` of the commutative ring `R`. -/
instance : has_top (my_ideal R) :=
⟨{carrier := set.univ,
  zero_mem' := set.mem_univ 0,
  mul_mem' := 
  begin
    intros a b ha,
    simp,
  end,
  sub_mem' := 
  begin
    intros a b ha hb,
    simp,
  end
}⟩ 

instance : inhabited (my_ideal R) := ⟨⊥⟩

/-- Since the bottom element is the (0) ideal, therefore, any element in it will be 0. -/
@[simp]lemma mem_bot {x : R} : x ∈ (⊥ : my_ideal R) ↔ x = 0 := set.mem_singleton_iff

/-- Since the top element is the whole commutative ring `R`, therefore, an element 
belonging to the top element belongs to the commutative ring `R`. -/
@[simp]lemma mem_top (x : R) : x ∈ (⊤ : my_ideal R) := set.mem_univ x

/-- The inf of two ideals is their intersection. -/
instance : has_inf (my_ideal R) :=
⟨λ I J,
  { carrier := I ∩ J,
    zero_mem' := 
    begin
      fconstructor,
      apply zero_mem,
      apply zero_mem,
    end,
    mul_mem' := 
    begin
      intros a b c,
      fconstructor,
      simp at c,
      cases c,
      simp,
      apply mul_mem,
      exact c_left,
      simp at c,
      cases c,
      simp,
      apply mul_mem,
      exact c_right,
    end,
    sub_mem' := 
    begin
      intros a b c d,
      simp at c,
      simp at d,
      cases c,
      cases d,
      simp,
      split,
      apply sub_mem,
      exact c_left,
      exact d_left,
      apply sub_mem,
      exact c_right,
      exact d_right,
    end
  }
⟩

/-- The infimum of possibly an infinitely many ideals is also their intersection.-/
instance : has_Inf (my_ideal R) :=
⟨λ S,
{ carrier := ⋂ t ∈ S, ↑t,
  zero_mem' := set.mem_bInter $ λ i h, i.zero_mem,
  mul_mem' := λ x y hy, set.mem_bInter $ λ i h,
    i.mul_mem (by apply set.mem_bInter_iff.1 hy i h),
  sub_mem' := λ x y hx hy, set.mem_bInter $ λ i h,
    i.sub_mem (by apply set.mem_bInter_iff.1 hx i h) (by apply set.mem_bInter_iff.1 hy i h) }⟩

/-
The union of two ideals is not necessarily an ideal. For example, the ideals `2ℤ` and `3ℤ` in 
the ring `ℤ`, have their union as `2ℤ ∪ 3ℤ` but this is not an ideal as it does not contain 
the element `2+3=5`, hence, fails to be a subring.

Hence, the union of two ideals is a subring ↔ one ideal ≤ another ideal. 

So, one can certainly say that the union of two ideals cannot be their supremum. For any ideal
to be the union, it must definitely contain the two ideals as well as be closed under addition.

Therefore, the ideal `I + J` fulfills the two criterion and hence, "can" be the supremum.

The file will later investigate if the claim that my_ideal `I + J` is same as the supremum of ideals
defined by Lean under the name `has_sup`, represented by `I ⊔ J`.
-/

/-- Defining `has_add` to be the sum of two ideals: -/
instance : has_add (my_ideal R) :=
⟨λ I J, { carrier   := {x | ∃ (i ∈ I) (j ∈ J), x = i + j},
  zero_mem':= 
  begin 
    simp at *,
    fconstructor,
    exact ring.zero,
    fconstructor,
    exact zero_mem I,
    fconstructor,
    exact ring.zero,
    fconstructor,
    exact zero_mem J,
    exact self_eq_add_left.mpr rfl,
  end,
  mul_mem' := 
  begin
    intros a b ha,
    cases ha with m hm,
    dsimp,
    use (a*m),
    split,
    change ∃ (H : m ∈ I) (k : R) (H : k ∈ J), b = m + k at hm,
    apply mul_mem I,
    finish,
    cases hm with t ht,
    cases ht with p hp,
    use (a*p),
    split,
    apply mul_mem J,
    finish,
    simp at *,
    cases hp,
    rw hp_right,
    apply mul_add,
  end,
  sub_mem' := 
  begin 
    intros a b ha hb,
    cases ha with m hm,
    cases hb with n hn,
    cases hm with p hp,
    cases hn with q hq,
    cases hp with s hs, cases hq with t ht,
    dsimp,
    cases hs with x hx, 
    cases ht with y hy,
    use (m-n),
    split,
    finish,
    use (s-t),
    split,
    finish,
    rw hx,
    rw hy,
    exact add_sub_comm m s n t,
  end }⟩

-- Advancing towards giving ideals the structure of a complete lattice:

/-
Having defined inclusion - also directly implied by the instance `set_like`, top ⊤ element and 
the bottom ⊥ element, the meet of ideals given by `has_inf` and `has_Inf`, which generates the
join of ideals `has_sup` and `has_Sup` by taking the infimum of all the ideals which contain the 
two ideals `I, J`, we now give `my_ideal R` the structure of a compelete lattice.
-/

/-- The instance `complete_lattice` defines the complete lattice formed by ideals of the form 
`my_ideal R`. -/
instance : complete_lattice (my_ideal R) :=
{ le           := (≤),
  lt           := (<),
  bot          := (⊥),
  bot_le       := λ S x hx, (mem_bot.1 hx).symm ▸ S.zero_mem,
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (my_ideal R) $ λ s,
    is_glb.of_image (λ S T,
      show (S : set R) ≤ T ↔ S ≤ T, from set_like.coe_subset_coe) is_glb_binfi }

/-
The `complete_lattice` defines a complete lattice formed by ideals without explicitly 
defining `has_sup` or `has_Sup` as, it generates them by using `has_inf` and `has_Inf`. 

However, I claimed that `has_add` is the supremum of ideals of the form `my_ideal`, and hence,
I will try to prove that is it same as the `has_sup` defined for ideals by Lean.
-/

/-- Introducing a lemma to provide a more defined structure to the elements in `I + J`. -/
@[simp] lemma has_add_mem (x : R) : x ∈ I + J ↔ ∃ (i ∈ I) (j ∈ J), x = i + j := 
begin
  split,
  tauto,
  itauto,
end

-- Proof that the claim is true :

/-- Proving that `has_add` represented by `I + J` is same as `has_sup` defined by Lean and
represented by `I ⊔ J`. -/
lemma has_add_eq_has_sup : I + J = I ⊔ J := 
begin
  apply ext,
  intro x,
  split,
  intro a,
  simp at *,
  cases a with p hp,
  cases hp with q hq,
  cases hq with r hr,
  cases hr with s hs,
  rw hs,
  have hv1 : J ≤ I ⊔ J,
  finish,
  have hv : r ∈ I ⊔ J,
  tauto,
  have hu1 : I ≤ I ⊔ J,
  finish,
  have hu : p ∈ I ⊔ J,
  tauto,
  finish,
  suffices : I ⊔ J ≤ I + J,
  tauto,
  have h1: I ≤ I + J,
  intros a b,
  simp at *,
  use a,
  split,
  exact b,
  use 0,
  split,
  apply zero_mem J,
  rw add_zero,
  have h2: J ≤ I + J,
  intros a b,
  simp,
  use 0,
  split,
  apply zero_mem I,
  use a,
  split,
  exact b,
  rw zero_add,
  apply sup_le h1 h2,
end

/-
This part of code although not required, is still present in the file, as it was used
to confirm if certain structures have been defined automatically by `complete_lattice`

example : has_le (my_ideal R) := by apply_instance

example : partial_order (my_ideal R) := by apply_instance

example : lattice (my_ideal R) := by apply_instance

example : complete_lattice (my_ideal R) := by apply_instance

example : has_lt (my_ideal R) := by apply_instance

example :  has_sup (my_ideal R) := by apply_instance

example :  semilattice_sup (my_ideal R) := by apply_instance
-/

/-
Since the motivation behind the project- to give ideals a structure of complete lattice, 
has been fulfilled, the namespace `my_ideal` and section `comm_ring` can be closed.
-/

end my_ideal
end comm_ring

#lint
