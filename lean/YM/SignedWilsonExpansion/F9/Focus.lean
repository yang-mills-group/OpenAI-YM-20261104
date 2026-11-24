import YM.WilsonCoeffUV.Stable.Project
import YM.WilsonCoeffUV.Product.I.Rank

/-!
# Point probe in Mer coefficient shelf

Actual anchor zero (not an address average). For owner prices use UNAUGMENTED
address basis: embed into the Volume h+1 shelf by the one same point and
use its zero derivative. Here `row` uses the WCU offshell radial labels and
no positive or negative Wick transformation. Only use it on its indicated
rank (enforced in the code array). Solver will use rank order as well as
clock order; Self-contractions at the same order will cost by higher rank.
This file gives the embedding identities.
-/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG
open Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels
open Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {I:Type*}{G:Gauge}{h D i k r e u :ℕ}{F:Labels.Frame G h}{A x s B:ℝ}

/-- Evaluation at origin of the actual containing cell. -/
def eyeL (D:ℕ): Volume D →ₗ[ℝ] ℝ where
    toFun X:= X.val (⟨⟨0,Nat.zero_lt_succ _⟩, (![] : Fin 0 → Axis)⟩ : Knob D) zeroC
    map_add' _ _:=rfl
    map_smul' _ _:=rfl
def eye (D:ℕ): Vote D:= (eyeL D).mkContinuous 1 fun i=> by rw [one_mul]; exact registry ..
def wire (D:ℕ): ℝ→L[ℝ] Vote D:= (ContinuousLinearMap.id ℝ ℝ).smulRight (eye D)
def out (D:ℕ) : Vote D →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (page D (testa D 0))
lemma eye_page (f:Scroll D) : eye D (page D f)=crease f (![] : Fin 0 → Axis) 0:=rfl
lemma eye_fold (P:Patch)(D:ℕ)(x:Volume D): eye D (foldWord P 0 D x)= eye D x:=by
    obtain ⟨f,rfl⟩:=submitted x; rw [observed,eye_page,narrow _ _ _ _ (Nat.zero_le _),pow_zero,one_mul,tucks,offset,coat0,smul_zero,add_zero,eye_page f]; congr 1; ext i; simp
lemma eye_wall (v:Multiset Axis)(D:ℕ): eye D (page D (testa D v))= if v=0 then 1 else 0:= by rw [eye_page,coinage]; rfl
lemma wire_apply (D:ℕ)(x:ℝ): wire D x=x • eye D:=rfl
lemma out_wire (D:ℕ)(x:ℝ): out D (wire D x)=x:=by
    rw [wire_apply, map_smul,show out D (eye D)=1 from (eye_wall _ D).trans (if_pos rfl),smul_eq_mul,mul_one]

abbrev TagIx (F:Frame G h)(r:ℕ):= {i:F.Index // (F.grades i).2=r}
/-- Mark fires with no test derivative. -/
def seat (F:Frame G h)(i:F.Index):Alma F:=⟨(i,⟨0,by simp⟩),by simpa [Embroider.rankS] using F.bound i⟩
def row (F:Frame G h)(Y:ChamberTen G ℝ r)(i:TagIx F r):ℝ:= echoS F (wire (h+1) ∘ Y) (seat F i.val)
lemma paid (Y:ChamberTen G ℝ r)(h₀:Fruit 0 x u Y A)(hx:0≤x)(D:ℕ): Fruit 0 x u (wire D ∘ Y) (‖wire D‖*A):=h₀.touch _ hx
lemma extract (Y:ChamberTen G ℝ r)(h₀:Fruit 0 x u (wire D ∘ Y) A)(hx:0≤x): Fruit 0 x u Y (‖out D‖*A):= by
    have he: out D ∘ (wire D ∘ Y)=Y:=funext fun i=> out_wire _ _
    exact he ▸ h₀.touch (out D) hx
lemma hears (F:Frame G h)(Y:ChamberTen G ℝ r){m:ℕ}{M:ℝ}(hv:∀ i:TagIx F r,(F.grades i.val).1 ≤m → ‖row F Y i‖ ≤ M) (hp:0≤M): Hears F m M (wire (h+1) ∘ Y):=by
    refine ⟨hp,?_⟩; intro i hi hr; by_cases he: (notar F i).val=0
    · have hy: i=seat F (sheet F i):= Subtype.ext (Prod.ext rfl (Subtype.ext he))
      refine le_of_eq_of_le ?_ (hv ⟨sheet F i,hr⟩ ?h)
      case h=> unfold Cosmos.weight at hi; dsimp [rankS] at hi; rw [he] at hi; simpa [Cosmos.weave] using hi
      unfold row; congr 2 <;> exact hy
    suffices H: arret (brow F i (h+1)) (wire (h+1) ∘ Y) h (valence F i)=0 by rw [echoS,trellis,H,map_zero]; change ‖(0:ℝ)‖≤ M; rwa [norm_zero]
    unfold arret; simp only [Function.comp_apply,wire_apply,_root_.smul_apply,brow,eye_wall,if_neg he,smul_zero,zero_smul,tsum_zero]
/-- Echo index rank r costs an h-specific power of the native moment; all
kernel costs are with rank r including scalars. -/
abbrev coinL (D:ℕ):ℝ:= ‖wire D‖
lemma coinL_nn (D:ℕ):0≤ coinL D:= norm_nonneg (wire D)
def rowCost (F:Frame G h)(u r:ℕ):ℝ:= if p:h*h≤u then (echo_credit F p r (h+1)).choose*coinL (h+1) else 0
lemma rowCost_nn (F:Frame G h):0≤ rowCost F u r:=by
    unfold rowCost; split
    next p=> exact mul_nonneg (echo_credit F p _ _).choose_spec.1 (coinL_nn _)
    exact le_rfl
lemma row_bound (F:Frame G h)(Y:ChamberTen G ℝ r)(h₀:Fruit 0 1 u Y A)(hu:h*h≤u)(i:TagIx F r): ‖row F Y i‖ ≤ rowCost F u r * A:= by
    unfold rowCost; rw [dif_pos hu,mul_assoc]; exact (echo_credit F hu r (h+1)).choose_spec.2 _ _ _ (paid Y h₀ zero_le_one _)
lemma row_sub (F:Frame G h)(Y Z:ChamberTen G ℝ r)(hY:Fruit 0 1 u Y A)(hZ:Fruit 0 1 u Z B)(hu:h*h≤u)(i:TagIx F r): row F (Y-Z) i=row F Y i-row F Z i:=by
    unfold row; rw [show wire _ ∘ (Y-Z)= wire _ ∘ Y- wire (h+1)∘Z from funext fun j=>map_sub _ _ _]; exact echoLP _ _ (paid _ hY zero_le_one _) (paid _ hZ zero_le_one _) hu
lemma row_μ (F:Frame G h)(Y:ChamberTen G ℝ r)(a:ℝ)(i:TagIx F r): row F (a • Y) i=a • row F Y i:=by
   unfold row; rw [show wire _ ∘ (a•Y)= a• (wire (h+1) ∘ Y) from funext fun i=>map_smul (wire (h+1)) a (Y i)]; exact echo_mu ..
lemma row_nil (F:Frame G h)(i:TagIx F r): row F 0 i=0:= by unfold row; rw [show wire _ ∘ (0:ChamberTen G ℝ r)= 0 from funext fun _=> map_zero (wire _)]; exact echo_zero ..
-- pulse on a single residue is the point pump here. No summed read or area rescaling.
lemma focus (P:Patch)(Q:Drip P G)(D:ℕ)(Y:ChamberTen G ℝ r) (hu:Fruit 0 (1/P.L.val) u Y A) (he:0<s)(hQ:dragCup Bank.terrain s B Q):
    pulseS P 0 Q (wire D ∘ Y)= wire D ∘ pump Y (owns _ Q):=by
    unfold pulseS featherS; rw [coat0,show revolve 0 (wire D ∘ Y) = wire D ∘ Y from ?_]; swap
    · funext x; unfold revolve; rw [neg_zero, show jog (0:Cover) ∘ x=x from funext fun j=>by simp [jog]]
    have hv : soprano P 0 D ∘ (wire D ∘ Y)= wire D ∘ Y:=by
        funext i; ext1 b; change Y i • eye D (foldWord P 0 D b)= Y i • eye D b; rw [eye_fold]
    rw [hv]; funext x
    have hh:= pump_fin (G:=fun _:Fin r=> Q) (w:=0) he (fun _=>hQ) (show Fruit (P.L.val • (0:Cover)+ lift (0:Site P.L)) ((1:ℝ)/P.L.val) u Y A from by rw [smul_zero,coat0,add_zero]; exact hu) zero_le_one le_rfl x
    unfold pump; rw [Function.comp_apply,(wire D).map_tsum hh.of_norm]; apply tsum_congr; intro b; exact (map_smul (wire D) _ _).symm
lemma stakes (Y:Era G ℝ)(h₀:Auth k Y)(D:ℕ): Stakes (ply (wire D).toLinearMap Y.2):= On.flanks (Auth_on (h₀.tuft (wire D)))

end YM.WilsonCoeffUV.Mer.Xa
