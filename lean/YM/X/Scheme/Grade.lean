import YM.X.Rank.Zoom
import YM.PertExtension.PureBasis
/-!
Operator engineering grades & slot number. Define by eigenvalues on Label coords upstairs using `Pert.RawLabels.fixedPolynomial`, known ℝ&Ortho natural on free fields. The section construction requires a pure right inverse. Use for lifts across all horizons.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Function Filter Set Maxwell Maxwell.Free Wick Labels Pert Pert.RawLabels Pert.Position Extra.FD
open scoped Topology BigOperators Classical
variable {G:Gauge} (F:Frames G) {d e : ℕ} (f:ℕ×ℕ→ℂ)
local notation "B" => F.level d
local notation "D" => Label G d
local notation "W" => E F d

def scaledPol (X : Labels.Frame G d) (f:ℕ×ℕ→ℂ) : Module.End ℂ (Label G d) := X.coords.symm.toLinearMap ∘ₗ LinearMap.pi (fun i => f (X.grades i) • ((LinearMap.proj i) ∘ₗ X.coords.toLinearMap))
lemma scalePol_eq (q:D) (i) : (F.level d).coords (scaledPol B f q) i = f ((F.level d).grades i)* (F.level d).coords q i:= by unfold scaledPol; rw [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]; rfl
lemma scalePol_pure {m : ℕ×ℕ}(q:D)(hq:q∈ Labels.Grade m): scaledPol B f q= f m • q:= by apply (F.level d).coords.injective; funext i; rw [scalePol_eq F,map_smul,Pi.smul_apply,smul_eq_mul]; by_cases h:m=(F.level d).grades i; rw [h]; rw [(F.level d).power_coefficient i h hq];simp
section
-- a useful universal commutation
variable {F} {A : Labels.Frames G}
lemma scalePol_commute {s:ℂ→+*ℂ}(g:ℕ×ℕ→ℂ)(T : (Label G d) →ₛₗ[s] (Label G e))(ht: ∀ m q,q ∈ Labels.Grade m → T q∈ Labels.Grade m) (h : ∀ i,s (f i)=g i) : (scaledPol (A.level e) g).comp T=T.comp (scaledPol (F.level d) f) := by
    apply (F.level d).basis.ext
    intro i; let m:= (F.level d).grades i
    have he : ((F.level d).basis i)∈Labels.Grade m := (F.level d).pure i; have he' : T _∈ Labels.Grade m:= ht m _ he
    simp only [LinearMap.comp_apply]; rw [scalePol_pure A g _ he', scalePol_pure F f _ he,map_smulₛₗ,h]
end
lemma physical_inj : Injective (physicalLabel F d):= by intro p q hp; rw [← physical_round F p,← physical_round F q,hp]
lemma fixedGrade {m}(q:D)(h:q∈ Labels.Grade m) : fixedPolynomial G d q ∈ Labels.Grade m:= by
   have he:= gradePart_mem m (fixedPolynomial G d q); rw [fixed_pure,gradePart_self q _ h] at he; exact he
lemma scalePol_fixed (q:D): scaledPol B f (fixedPolynomial G d q)= fixedPolynomial G d (scaledPol B f q) := DFunLike.congr_fun (scalePol_commute (F:=F) f f _ (fun _=>fixedGrade) (fun _=>rfl)) q

def scalePolDiff (F:Frames G) (f:ℕ×ℕ→ℂ) (d:ℕ) : Module.End ℂ (E F d) := enroll F d ∘ₗ scaledPol (F.level d) f ∘ₗ physicalLabel F d
lemma scalePol_enroll (q:D): scalePolDiff F f d (enroll F d q)=enroll F d (scaledPol B f q):= by rw [scalePolDiff]; simp only [LinearMap.comp_apply,embed_round,scalePol_fixed F,enroll_fixed]
local notation "Γ" => scalePolDiff F
lemma scalePol_physical (q:W): physicalLabel F d (Γ f d q)=scaledPol B f (physicalLabel F d q):= by
   conv_lhs=> rw [← physical_round F q]
   rw [scalePol_enroll,embed_round, ← scalePol_fixed F]; apply congr_arg _; apply Subtype.ext; exact flat_idem _
lemma scalePol_up (h:d≤e)(q): up F h (Γ f d q)=Γ f e (up F h q):= by
   apply physical_inj; simp only [up, physical_inclusion F (scheme_filters F), scalePol_physical F]; exact (DFunLike.congr_fun (scalePol_commute f f (raiseLabel G h) (fun _ _ h=> h) (fun _=>rfl)) _).symm
lemma scalePol_star (g:ℕ × ℕ → ℂ)(h : ∀ i,star (f i)=g i)(q:W): (Model F).conj (hierarchy F).spin d (Γ f d q)=Γ g d ((Model F).conj (hierarchy F).spin d q):= by
   have H (i)(q:Label G d)(hq:q∈Labels.Grade i): realBar q∈Labels.Grade i:= by
      have he:=gradePart_mem i (realBar q); rw [gradePart_bar,gradePart_self q _ hq] at he; exact he
   apply physical_inj
   simp only [physical_real F,scalePol_physical F]; exact (DFunLike.congr_fun (scalePol_commute f g realBar H h) _).symm
lemma scalePol_spin (s:Ortho)(q:W): rideO F s d (Γ f d q)=Γ f d (rideO F s d q):= by
   have H (i)(q:D)(h:q∈Labels.Grade i): Labels.tensor s q∈Labels.Grade i:= by
      have he:=gradePart_mem i (Labels.tensor s q); rw [gradePart_turn,gradePart_self q _ h] at he; exact he
   apply physical_inj; simp only [physical_ortho F,scalePol_physical F]; exact (DFunLike.congr_fun (scalePol_commute (A:=F) (F:=F) f f (Labels.tensor s) H (fun _=>rfl)) _).symm
lemma scalePol_unit : Γ f d ((Model F).unit d)=f (0,0) • ((Model F).unit d):= by
   apply physical_inj; rw [map_smul,scalePol_physical,physical_unit F]; exact scalePol_pure F f _ (unit_grade _)
lemma scalePol_mul (g:ℕ×ℕ→ℂ)(q:W): Γ f d (Γ g d q)=Γ (f*g) d q:= by
   apply physical_inj; apply (F.level d).coords.injective; funext i; simp only [scalePol_physical F,scalePol_eq F,Pi.mul_apply, mul_assoc]
lemma scalePol_one (q:W): Γ 1 d q=q:= by
   apply physical_inj; apply (F.level d).coords.injective; funext i; simp only [scalePol_physical F,scalePol_eq F,Pi.one_apply,one_mul]
lemma scalePol_zero (q:W): Γ 0 d q=0:= by apply physical_inj; apply (F.level d).coords.injective; funext i; rw [scalePol_physical, scalePol_eq]; simp
section prune
def prune (d : ℕ) : ℕ × ℕ → ℂ:= fun a=> if a.1≤d then 1 else 0
def trim (d e:ℕ) : Module.End ℂ (E F e):= Γ (prune d) e
lemma trim_self (h : d≤e)(q:W): trim F e d q=q:= by
   apply physical_inj; apply (F.level d).coords.injective; funext i; rw [trim,scalePol_physical,scalePol_eq]; simp [prune,((F.level d).bound i).trans h]
lemma trim_lower (h : d≤e) (q:E F e): trim F d e q∈lower F d e:= by
   let C:=F.level e; let x:= physicalLabel F e q; change enroll F e (scaledPol C (prune d) x)∈ _
   rw [← C.basis.sum_equivFun x,map_sum,map_sum]; apply (lower F d e).sum_mem; intro i hi
   have hz : scaledPol C (prune d) (C.basis i)=prune d (C.grades i) • C.basis i:= scalePol_pure F (prune d) _ (C.pure i)
   simp only [map_smul,hz]; apply (lower F d e).smul_mem; by_cases he:(C.grades i).1 ≤ d
   · apply (lower F d e).smul_mem; rw [up_pre F h]
     let v:= PertExtension.Horizon.lowered C i; refine ⟨enroll F d (raiseLabel _ he v),?_⟩
     change up F h (UVNext.FreeStress.embed F _ _)=_; rw [up,UVNext.FreeStress.rise_embed F _ (scheme_filters F)]; rfl
   · simp only [prune,if_neg he,zero_smul,zero_mem]
end prune
end YM.PositionX
