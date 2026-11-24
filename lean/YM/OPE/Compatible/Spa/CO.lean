import YM.OPE.Compatible.Aq.Brace
/-!
# Radical complement engineering. τ-all phases. Finite exposed algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Set Function
open scoped Topology BigOperators Classical
-- Turns.K generic prism ν
variable {E F Z M:Type}[AddCommGroup E][Module ℝ E][AddCommGroup F][Module ℝ F][AddCommGroup Z][Module ℝ Z]
abbrev Jewel (E:Type):= Fin 3→ E
def τΓ (E:Type)[AddCommGroup E][Module ℝ E] : Jewel E→ₗ[ℝ] Jewel E where
     toFun x:= ![0,x 0,x 1]
     map_add' p q:=funext (fun i=> by fin_cases i<;>first|rfl | exact (add_zero _).symm)
     map_smul' c p:= funext (fun i=> by fin_cases i <;> first|rfl| exact (smul_zero c).symm)
lemma τRide (x:Jewel E) : τΓ E x 0=0 ∧ τΓ E x 1=x 0∧τΓ E x 2=x 1:= ⟨rfl,rfl,rfl⟩
lemma τnil (x:Jewel E):τΓ E (τΓ E (τΓ E x))=0:=by funext i;fin_cases i<;>rfl
lemma τRise (x:E)(i:Fin 3): Pi.single i x=(τΓ E^i.val) (Pi.single 0 x):=by
      fin_cases i; · rfl
      · change Pi.single 1 x = (τΓ E^1) _; rw[pow_one]; ext j; fin_cases j <;> simp [τΓ]
      change Pi.single 2 x=(τΓ E^2) _; rw [pow_two]; funext j; change (Pi.single 2 x:Jewel E) j= τΓ E (τΓ E (Pi.single 0 x)) j; fin_cases j <;> simp [τΓ]
noncomputable def jewelMap (f:E→ₗ[ℝ] F): Jewel E →ₗ[ℝ] Jewel F:= LinearMap.pi (fun i:Fin 3=> f.comp (LinearMap.proj i))
lemma JMic (f:E→ₗ[ℝ] F)(x:Jewel E): τΓ F (jewelMap f x)=jewelMap f (τΓ E x):=by
      funext j;fin_cases j<;>first|rfl| exact (map_zero f).symm
structure Horb (π:E→ₗ[ℝ] F)(σ:E→ₗ[ℝ] E)(f:E≃ₗ[ℝ] Jewel F):Prop where
     top (x:E):π x=f x 0
     inverse' (x:E):f (σ x)=τΓ F (f x)
-- Radical through turns Leader detection.
variable {π:E→ₗ[ℝ] F}{σ:E→ₗ[ℝ] E}{f:E≃ₗ[ℝ] Jewel F}{U W:Submodule ℝ F}{Y:Submodule ℝ E}
noncomputable def marchL (f:E≃ₗ[ℝ] Jewel F)(W:Submodule ℝ F): Jewel W→ₗ[ℝ] E:= f.symm.toLinearMap.comp (jewelMap W.subtype)
lemma march_cm (h:Horb π σ f)(x:Jewel W): marchL f W (τΓ (↥W) x)=σ (marchL f W x):=by
      unfold marchL; apply f.injective; simp only [h.inverse', LinearMap.comp_apply,LinearEquiv.coe_coe,f.apply_symm_apply,JMic]
lemma Mway (f:E≃ₗ[ℝ] Jewel F)(x:Jewel W)(i:Fin 3): (x i).val=f (marchL f W x) i:=by rw [marchL,LinearMap.comp_apply, LinearEquiv.coe_coe, f.apply_symm_apply];rfl
structure Flank (f:E≃ₗ[ℝ] Jewel F)(σ:E→ₗ[ℝ] E)(U W: Submodule ℝ F)(Y:Submodule ℝ E):Prop where
     decmp : IsCompl U W
     τZ (x:E)(h:x∈Y):σ x∈Y
     kill (x:E)(hx:x∈Y)(i:Fin 3)(hp:∀ j:Fin 3,j < i →f x j=0): f x i∈U
     toll (x:F)(h:x∈U): ∃ p∈Y,x=f p 0
lemma compass (H:Flank f σ U W Y)(x:Jewel W)(h:marchL f W x∈Y):x=0:=by
      suffices he:∀ n:ℕ,∀ i: Fin 3,i.val=n→ x i=0 by exact funext (fun i=> he i.val i rfl)
      intro n; induction n using Nat.strong_induction_on with| h n ih=> intro i hi; subst n; apply Subtype.ext; refine Submodule.disjoint_def.mp H.decmp.disjoint _ ?_ ((x i).property); rw [Mway f]; exact H.kill _ h i (fun j hj=> ((Mway f x j).symm.trans (congr_arg Subtype.val (ih j.val hj j rfl))))
end YM.OPE.Hark
