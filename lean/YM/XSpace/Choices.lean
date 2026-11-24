import YM.XSpace.Parity

/-!
# Choose square, real position systems, jointly nested & parity intertwining
Every row is a finite real linear combination of observations (`windows`)
criterion, on ALL correl tests with that horizon. In particular upper
horizon positions prepend all lower ones literally (using this system after
engineering reannouncement; the zeroth order solution can be nested). Keep
this fixed for every formal calculation, not order adaptive.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d l:ℕ}

structure Screen (G:Gauge) (d:ℕ) where
  D : Prediction G d→ₗ[ℝ] Change G d
  observable : ∃ (n:ℕ) (w:Fin n→Window G d) (P:(Fin n→ℂ)→ₗ[ℝ] Change G d), ∀ U: Prediction G d,D U=P fun i=> watch (w i) U

namespace Screen
def Prepared (A: Screen G d): Prop:= (∀ T:Change G d,A.D (gradient G d T)=T) ∧ ∀ P:Prediction G d,A.D (recruit (hinge d) P)=arch d (A.D P)
def carry (A:Screen G d) (F:Sec G d→ₗ[ℂ] Sec G l) (L:(Change G d)→ₗ[ℝ] Change G l): Screen G l where
  D:= L ∘ₗ A.D ∘ₗ ((recruit F).restrictScalars ℝ)
  observable := by
    obtain ⟨n,w,P,h⟩:= A.observable
    refine ⟨n,fun i=> ⟨_,(w i).t,F ∘ (w i).p⟩, L ∘ₗ P, fun U=>?_⟩; change L (A.D (recruit F U))=_; rw [h]; rfl
lemma carries (A:Screen G d) (F:Sec G d→ₗ[ℂ] Sec G l) (L:(Change G d)→ₗ[ℝ] Change G l) (P:Prediction G l): (A.carry F L).D P=L (A.D (recruit F P)):=rfl

def mergeS (A B: Screen G d): Screen G d where
  D:= A.D+B.D
  observable:=by
    obtain ⟨n,w,P,h⟩:= A.observable; obtain ⟨m,v,Q,hq⟩:= B.observable
    let z := Fin.append w v
    let a : (Fin (n+m)→ℂ)→ₗ[ℝ] (Fin n→ℂ):= LinearMap.pi (fun x=> LinearMap.proj (Fin.castAdd m x)); let b : (Fin (n+m)→ℂ)→ₗ[ℝ] (Fin m→ℂ):= LinearMap.pi (fun x=> LinearMap.proj (Fin.natAdd n x))
    refine ⟨n+m,z,(P ∘ₗ a)+(Q ∘ₗ b),fun U=>?_⟩; rw [LinearMap.add_apply,LinearMap.add_apply,h,hq]; simp only [LinearMap.comp_apply]
    congr 2 <;> ext1 i <;> simp [a,b,z]
lemma merged (A B:Screen G d) (P: Prediction G d): (A.mergeS B).D P=A.D P+B.D P:= rfl

lemma recruit_one (P:Prediction G d): recruit (1:FieldEnd G d) P=P:=rfl
lemma choose_all (g:G.Simple) (d:ℕ): ∃ A:Screen G d,A.Prepared:=by
  obtain ⟨K,hk⟩:= choose_window (d:=d) g ⊤; let V : Submodule ℝ (Change G d):= ⊤; let T: Screen G d:= ⟨V.subtype ∘ₗ K.diagnostic,⟨K.n,K.w, V.subtype ∘ₗ K.read,fun _=>rfl⟩⟩
  have he (p: Change G d): T.D (gradient G d p)=p:= congr_arg Subtype.val (hk (⟨p, by trivial⟩))
  let S:=LinearMap.id (R:=ℝ) (M:=Change G d); let U:= (T.mergeS (T.carry (hinge d) (arch d))).carry (1:FieldEnd G d) ((2:ℝ)⁻¹ • S)
  have h (P): U.D P=(2:ℝ)⁻¹ • (T.D P+arch d (T.D (recruit (hinge d) P))):= rfl
  refine ⟨U,fun p=> ?_,fun P=>?_⟩
  · rw [h, gradient_arched, he,he, arches, ← two_smul ℝ, inv_smul_smul₀ (by norm_num)]
  rw [h,h,homes, map_smul,map_add,arches,add_comm (T.D _)]

def Next (A:Screen G d) (B:Screen G (d+1)):Prop := ∀ P: Prediction G (d+1),fell d (B.D P)=A.D (recruit (step d) P)

lemma advance (g:G.Simple) (A:Screen G d) (hA:A.Prepared): ∃ B,A.Next B ∧ B.Prepared:= by
  obtain ⟨T,ht⟩:= choose_all g (d+1); let L:=(LinearMap.id (M:=Change G (d+1)) (R:=ℝ))-(grow d ∘ₗ fell (G:=G) d); let B:= (A.carry (step d) (grow d)).mergeS (T.carry (1:FieldEnd G (d+1)) L)
  have he (P): B.D P=grow d (A.D (recruit (step d) P))+(T.D P-grow d (fell d (T.D P))):=rfl
  refine ⟨B,fun P=>?_,fun X=>?_,fun P=>?_⟩
  · rw [he,map_add, map_sub, renewed,renewed, sub_self,add_zero]
  · rw [he,recruits_slope, hA.1, ht.1]; abel
  rw [he, show recruit (step d) (recruit (hinge (d+1)) P)= recruit (hinge d) (recruit (step d) P) from rfl, hA.2, ht.2, ←arch_fell,he,map_add,map_sub,arch_grow, arch_grow]

end Screen

structure Choice (G:Gauge) where
  measure : ∀ d, Screen G d
  prepared : ∀ d,(measure d).Prepared
  respects : ∀ d,(measure d).Next (measure (d+1))

theorem choose_horizons (g:G.Simple) : Nonempty (Choice G):= by
  let A: ∀ d,{A:Screen G d//A.Prepared}:=fun n=>Nat.rec (motive:=fun n=>{A:Screen G n//A.Prepared}) ⟨(Screen.choose_all g 0).choose,(Screen.choose_all g 0).choose_spec⟩ (fun _ T=> ⟨(Screen.advance g T.val T.property).choose,(Screen.advance g T.val T.property).choose_spec.2⟩) n
  exact ⟨fun d=> (A d).val, fun d=> (A d).property,fun d=> (Screen.advance g (A d).val (A d).property).choose_spec.1⟩ -- nested ctor
end YM.XSpace.Normalize
