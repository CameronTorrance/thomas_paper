import ring_theory.tensor_product
import algebra.algebra.bilinear

open_locale tensor_product

universes ur uc

noncomputable theory

section missing_tensor_stuff

variables 
{R : Type*} [comm_semiring R]
{A : Type*} [ring A] [algebra R A]
{M₁ : Type*} [add_comm_monoid M₁] [module R M₁] 
{N₁ : Type*} [add_comm_monoid N₁] [module R N₁] 
{M₂ : Type*} [add_comm_monoid M₂] [module R M₂] 
{N₂ : Type*} [add_comm_monoid N₂] [module R N₂] 
{M₃ : Type*} [add_comm_monoid M₃] [module R M₃] 
{N₃ : Type*} [add_comm_monoid N₃] [module R N₃]

namespace tensor_product

lemma map_assoc (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) : 
  (↑(tensor_product.assoc R N₁ N₂ N₃)) ∘ₗ (tensor_product.map (tensor_product.map f₁ f₂) f₃)
  = (tensor_product.map (f₁ : M₁ →ₗ[R] N₁) (tensor_product.map f₂ f₃)) ∘ₗ 
  ↑(tensor_product.assoc R M₁ M₂ M₃) := 
begin
  apply tensor_product.ext',
  intros xy z,
  apply tensor_product.induction_on xy,
  { simp only [zero_tmul, map_zero] },
  { intros x y,
    simp only [linear_map.coe_comp, linear_equiv.coe_coe, function.comp_app, map_tmul,
       assoc_tmul] },
  { simp only [tensor_product.add_tmul, linear_map.coe_comp, linear_equiv.coe_coe, 
      function.comp_app, map_tmul, map_add],
    intros x y hx hy,
    rw [← hx,← hy] },
end

lemma lid_comm_ltensor (f₁ : M₁ →ₗ[R] N₁) : ↑(tensor_product.lid R N₁) ∘ₗ 
  (tensor_product.map (linear_map.id : R →ₗ[R] R) f₁) =  f₁ ∘ₗ ↑(tensor_product.lid R M₁) :=
by apply tensor_product.ext'; simp [linear_map.comp_apply]

lemma rid_comm_rtensor (f₁ : M₁ →ₗ[R] N₁) : ↑(tensor_product.rid R N₁) ∘ₗ 
  (tensor_product.map f₁ (linear_map.id : R →ₗ[R] R)) =  f₁ ∘ₗ ↑(tensor_product.rid R M₁) :=
by apply tensor_product.ext'; simp [linear_map.comp_apply]

end tensor_product

namespace algebra

/-
  translating algebra defns to statements about linear maps between
  vector spaces.
-/

lemma lmul'_assoc : (lmul' R : A ⊗ A →ₗ[R] A) ∘ₗ (_root_.tensor_product.map (lmul' R) 
  (linear_map.id : A →ₗ[R] A)) = (lmul' R : A ⊗ A →ₗ[R] A) ∘ₗ
  (_root_.tensor_product.map linear_map.id (lmul' R)) ∘ₗ ↑(_root_.tensor_product.assoc R A A A) :=
begin
  apply tensor_product.ext',
  intros xy z,
  apply tensor_product.induction_on xy,
  { simp only [tensor_product.zero_tmul, map_zero] },
  { intros x y,
    simp only[ mul_assoc, linear_map.coe_comp, function.comp_app,_root_.tensor_product.map_tmul, 
      lmul'_apply, linear_map.id_coe, id.def, linear_equiv.coe_coe, 
      _root_.tensor_product.assoc_tmul, eq_self_iff_true] },
  { simp only [tensor_product.add_tmul, linear_map.coe_comp, function.comp_app, 
      tensor_product.map_tmul, linear_map.id_coe, id.def, lmul'_apply, linear_equiv.coe_coe, map_add],
    intros x y hx hy,
    rw [←hx, ←hy] }
end

lemma algebra_map_id_left : (lmul' R : A ⊗ A →ₗ[R] A) ∘ₗ 
  (_root_.tensor_product.map (algebra.linear_map R A) linear_map.id) = 
  ↑(_root_.tensor_product.lid R A) := 
by apply tensor_product.ext'; simp[algebra.smul_def]

lemma algebra_map_id_right : (lmul' R : A ⊗ A →ₗ[R] A) ∘ₗ 
  (_root_.tensor_product.map linear_map.id (algebra.linear_map R A) ) = 
  ↑(_root_.tensor_product.rid R A) := 
by apply tensor_product.ext'; simp[← algebra.commutes, algebra.smul_def]

end algebra

end missing_tensor_stuff

class coalgebra (R : Type ur) [comm_semiring R] (C : Type uc) [add_comm_monoid C] [module R C] :=
(counit : C →ₗ[R] R)
(comul  : C →ₗ[R] (C ⊗[R] C))
(counit_left : ↑(tensor_product.lid R C) ∘ₗ (tensor_product.map counit linear_map.id) ∘ₗ comul = 
  (linear_map.id : C →ₗ[R] C))
(counit_right : ↑(tensor_product.rid R C) ∘ₗ (tensor_product.map linear_map.id counit) ∘ₗ comul =
  (linear_map.id : C →ₗ[R] C))
(coassoc : ↑(tensor_product.assoc R C C C) ∘ₗ (tensor_product.map comul linear_map.id) ∘ₗ comul = 
    (tensor_product.map linear_map.id  comul) ∘ₗ comul)

namespace coalgebra 

variables 
(R : Type*) [comm_semiring R]
(C : Type*) [add_comm_monoid C] [module R C] [coalgebra R C]
(A : Type*) [ring A] [algebra R A]

@[derive [add_comm_group, module R]]
def conv_alg := C →ₗ[R] A 

variables {R} {C} {A}

lemma coassoc' : (tensor_product.map comul linear_map.id) ∘ₗ (comul : C →ₗ[R] C ⊗ C) = 
  ↑(tensor_product.assoc R C C C).symm ∘ₗ (tensor_product.map linear_map.id comul) 
  ∘ₗ (comul : C →ₗ[R] C ⊗ C) :=
begin
  rw [←linear_equiv.to_linear_map_eq_coe ,linear_equiv.eq_to_linear_map_symm_comp],
  exact coassoc,
end

def grouplike_elm (c : C) : Prop := comul c = c ⊗ₜ[R] c

namespace conv_alg

instance : has_mul (conv_alg R C A) :=
 ⟨λ f g, (algebra.lmul' R) ∘ₗ (tensor_product.map f g) ∘ₗ comul⟩

@[simp] 
lemma mul_def (f g : conv_alg R C A) : 
  f * g = (algebra.lmul' R) ∘ₗ (tensor_product.map f g) ∘ₗ comul := rfl 

instance : has_one (conv_alg R C A) := ⟨(algebra.linear_map R A) ∘ₗ counit⟩

@[simp]
lemma one_def : (1 : conv_alg R C A) = (algebra.linear_map R A) ∘ₗ counit := rfl

instance : add_monoid_hom_class (conv_alg R C A) C A := linear_map.add_monoid_hom_class

lemma left_distrib (f g h : conv_alg R C A) : f * (g + h) = f * g + f * h := 
by simp [mul_def,tensor_product.map_add_right, linear_map.add_comp, linear_map.comp_add]

lemma right_distrib (f g h : conv_alg R C A) : (f + g) * h = f * h + g * h := 
by simp [mul_def,tensor_product.map_add_left, linear_map.add_comp, linear_map.comp_add]

lemma one_mul (f : conv_alg R C A) : 1 * f = f := 
begin
  simp only [one_def, mul_def],
  conv_lhs 
    begin 
      rw [← linear_map.id_comp f,tensor_product.map_comp, ← linear_map.comp_id f,
        ← linear_map.id_comp counit,tensor_product.map_comp],
    end,
  have hassoc : (algebra.lmul' R).comp 
      (((tensor_product.map (algebra.linear_map R A) linear_map.id).comp 
      ((tensor_product.map linear_map.id f).comp (tensor_product.map counit linear_map.id))).comp 
      (comul : C →ₗ[R] C ⊗ C)) = ((algebra.lmul' R : A ⊗ A →ₗ[R] A) ∘ₗ 
      (tensor_product.map (algebra.linear_map R A) linear_map.id)) ∘ₗ 
      (tensor_product.map linear_map.id f) ∘ₗ 
      ((tensor_product.map counit linear_map.id) ∘ₗ (comul : C →ₗ[R] C ⊗ C)),
    { simp only [linear_map.comp_assoc] },
  rw [hassoc, algebra.algebra_map_id_left, ←linear_map.comp_assoc,tensor_product.lid_comm_ltensor,
    linear_map.comp_assoc,counit_left],
  simp
end

lemma mul_one (f : conv_alg R C A) : f * 1 = f :=
begin
  simp only [one_def, mul_def],
  conv_lhs 
    begin 
      rw [← linear_map.id_comp f,tensor_product.map_comp, ← linear_map.comp_id f,
        ← linear_map.id_comp counit,tensor_product.map_comp],
    end,
  have hassoc : (algebra.lmul' R).comp 
      (((tensor_product.map linear_map.id (algebra.linear_map R A) ).comp 
      ((tensor_product.map f linear_map.id).comp (tensor_product.map linear_map.id counit))).comp 
      (comul : C →ₗ[R] C ⊗ C)) = ((algebra.lmul' R : A ⊗ A →ₗ[R] A) ∘ₗ 
      (tensor_product.map  linear_map.id (algebra.linear_map R A) )) ∘ₗ 
      (tensor_product.map f linear_map.id) ∘ₗ 
      ((tensor_product.map linear_map.id counit) ∘ₗ (comul : C →ₗ[R] C ⊗ C)),
    { simp only [linear_map.comp_assoc] },
  rw [hassoc, algebra.algebra_map_id_right, ←linear_map.comp_assoc,tensor_product.rid_comm_rtensor,
    linear_map.comp_assoc,counit_right],
  simp
end

lemma mul_assoc (f g h : conv_alg R C A) : f * g * h = f * (g * h) :=
begin
  simp only [mul_def],
  conv_rhs 
    begin
      congr, skip,
      rw [← linear_map.comp_id f, ← linear_map.comp_assoc,tensor_product.map_comp, 
        linear_map.comp_assoc, ← coassoc, ← linear_map.id_comp f, tensor_product.map_comp,
        linear_map.comp_assoc],
      congr, skip,
      rw [← linear_map.comp_assoc,← tensor_product.map_assoc],
    end,
  conv_rhs
    begin
      simp only [← linear_map.comp_assoc],
      congr, congr, congr,
      rw  [linear_map.comp_assoc, ← algebra.lmul'_assoc],
    end,
  simp[← tensor_product.map_comp, linear_map.comp_assoc],
end

instance : ring (conv_alg R C A) := {
  mul_assoc := mul_assoc,
  left_distrib := left_distrib,
  right_distrib := right_distrib,
  one_mul := one_mul,
  mul_one := mul_one,
  .. conv_alg.has_one,
  .. conv_alg.has_mul,
  .. (infer_instance : add_comm_group (conv_alg R C A))
}

instance : algebra R (conv_alg R C A) :=
begin
  apply algebra.of_module,
  { simp only [tensor_product.map_smul_left, linear_map.comp_smul, linear_map.smul_comp, mul_def,
     eq_self_iff_true, forall_const] },
  { simp only [tensor_product.map_smul_right, linear_map.comp_smul, linear_map.smul_comp, mul_def,
    eq_self_iff_true, forall_const] }
end

end conv_alg

end coalgebra

structure coalg_hom (R : Type*) [comm_semiring R] (C₁ : Type*) [add_comm_monoid C₁] [module R C₁] 
  [coalgebra R C₁] (C₂ : Type*) [add_comm_monoid C₂] [module R C₂] [coalgebra R C₂] :=
(to_map : C₁ →ₗ[R] C₂)
(map_counit' : (coalgebra.counit ∘ₗ to_map : C₁ → R) = coalgebra.counit) 
(map_comul' : coalgebra.comul ∘ₗ to_map  = (tensor_product.map to_map to_map) ∘ₗ coalgebra.comul)

infixr ` →ᶜ `:25 := coalg_hom _
notation A ` →ᶜ[`:25 R `] ` B := coalg_hom R A B

namespace coalg_hom

end coalg_hom

class bialgebra (R : Type*) [comm_semiring R] (B : Type*) [ring B] [algebra R B] extends 
  coalgebra R B :=
(counit_one : counit 1 = 1)
(counit_mul : ∀ x y : B, counit (x * y) = (counit x) * (counit y))
(comul_one : comul 1 = 1)
(comul_mul : ∀ x y : B,  comul (x * y) = (comul x) * (comul y))

class hopf_algebra (H : Type*) [ring H] {R : Type*} [comm_semiring R] [algebra R H] extends
  bialgebra R H :=
(id_unit : is_unit (linear_map.id : coalgebra.conv_alg R H H))
