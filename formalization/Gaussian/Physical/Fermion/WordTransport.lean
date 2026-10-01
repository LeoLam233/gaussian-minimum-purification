import Gaussian.Physical.Fermion.WardField

/-! Exact transport of operator words and their actual trace expectations. -/
noncomputable section
open scoped Matrix
namespace Gaussian.Physical.Fermion
variable {d α : Type*} [Fintype d] [DecidableEq d]

theorem inverse_conjugate_mul (U V A B : Matrix d d ℂ) (hVU : V*U=1) :
    U*(A*B)*V = (U*A*V)*(U*B*V) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V U,hVU,Matrix.one_mul]

/-- Generator transport determines transport of every finite ordered word. -/
theorem inverse_word_transport (U V : Matrix d d ℂ) (hUV : U*V=1) (hVU : V*U=1)
    (c f : α → Matrix d d ℂ) (hc : ∀ a, U*c a*V=f a) (l : List α) :
    U*(l.map c).prod*V = (l.map f).prod := by
  induction l with
  | nil => simpa using hUV
  | cons a l ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [inverse_conjugate_mul _ _ _ _ hVU,hc,ih]

/-- Word expectations in a transformed actual matrix are pulled back along its
proved generator action. -/
theorem matrixWordMoment_transform (D U V : Matrix d d ℂ) (hUV : U*V=1) (hVU : V*U=1)
    (c f : α → Matrix d d ℂ) (hc : ∀ a, V*c a*U=f a) (l : List α) :
    matrixWordMoment (U*D*V) c l = matrixWordMoment D f l := by
  unfold matrixWordMoment
  calc
    ((U*D*V)*(l.map c).prod).trace = (U*(D*V*(l.map c).prod)).trace := by
      simp [Matrix.mul_assoc]
    _ = ((D*V*(l.map c).prod)*U).trace := Matrix.trace_mul_comm _ _
    _ = (D*(V*(l.map c).prod*U)).trace := by simp [Matrix.mul_assoc]
    _ = (D*(l.map f).prod).trace := by rw [inverse_word_transport V U hVU hUV c f hc]

/-- Naturality of actual matrix moments under relabeling of field parameters. -/
theorem matrixWordMoment_map {β : Type*} (D : Matrix d d ℂ)
    (c : β → Matrix d d ℂ) (f : α → β) (l : List α) :
    matrixWordMoment D c (l.map f) = matrixWordMoment D (fun a => c (f a)) l := by
  simp [matrixWordMoment,List.map_map,Function.comp_def]

/-- A proved Wick rule is inherited by any subfamily of actual matrix fields. -/
theorem matrixWordMoment_wick_map {β : Type*} (D : Matrix d d ℂ)
    (c : β → Matrix d d ℂ) (f : α → β)
    (hW : ∀ l, matrixWordMoment D c l =
      wickValue (fun a b => matrixWordMoment D c [a,b]) l) (l : List α) :
    matrixWordMoment D (fun a => c (f a)) l =
      wickValue (fun a b => matrixWordMoment D (fun a => c (f a)) [a,b]) l := by
  rw [← matrixWordMoment_map, hW, wickValue_map]
  congr 1

/-- A proved generator implementation transports a Wick rule at the actual matrix level. -/
theorem matrixWordMoment_transform_wick (D U V : Matrix d d ℂ)
    (hUV : U*V=1) (hVU : V*U=1) (c f : α → Matrix d d ℂ)
    (hc : ∀ a, V*c a*U=f a)
    (hW : ∀ l, matrixWordMoment D f l =
      wickValue (fun a b => matrixWordMoment D f [a,b]) l) (l : List α) :
    matrixWordMoment (U*D*V) c l =
      wickValue (fun a b => matrixWordMoment (U*D*V) c [a,b]) l := by
  rw [matrixWordMoment_transform D U V hUV hVU c f hc,hW]
  congr 1
  funext a b
  exact (matrixWordMoment_transform D U V hUV hVU c f hc [a,b]).symm

end Gaussian.Physical.Fermion
