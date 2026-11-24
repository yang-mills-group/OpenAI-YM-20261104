import YM.GradedFar.Nook
/-!
# Empty Near price in M.1/M.2

Even for all-unit Near the replacement in the second inequality of M.2 is on exactly the unit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.Loft
open Finset Function Filter Set PowerSeries XSpace XSpace.Normalize XSpace.Structure1 Scale O O.Score
open Register Dframe O O.Score O.Enh O.Bind
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open scoped Topology BigOperators Classical
variable {G:Gauge} {n m l p k n' h:ℕ} (N:WilsonPrescription G){hG:G.Simple}
    {Z:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{σ:Prescription (Press.portDeck G)} (H:Main.Match N hG Z σ true)
local notation "A"=> Scale.Measure.outlook N.scheme N.criterion
local notation "Ω"=> install A
local notation "V"=> PowerSeries ℂ
private def space (h:ℕ):Fin 0→ℕ:=fun _=>h
private def Λ (h:ℕ): AppointedH140Inputs G (Output h):= fun _=> Normalize.leaf G h
private def leave : Fin 0↪ Fin n:=⟨ Fin.elim0, injective_of_subsingleton _⟩
private def vacancy (h:ℕ)(b:Q G) : V:= if hh:heft b≤h then PowerSeries.C (coord (low b hh) (Normalize.leaf G h)) else 0
lemma vacancy_flash (b:Toon G h): vacancy h (Dframe.flash b) = PowerSeries.C (coord b (Normalize.leaf G h)):= dif_pos (size_le b)
include H
lemma furniture (y:Points m)(v:Scan G m)(h:ℕ): Lamp Ω h y v (vacancy h)= porch N (Λ h) 0 y v:=by
 ext1 k; rw [show Lamp Ω h y v (vacancy h)=∑ i:Toon G h,vacancy h (Dframe.flash i) * lonelyG Ω y (Dframe.flash i) v from (LampT ..).symm]
 simp_rw [vacancy_flash,map_sum (coeff k), coeff_C_mul]; let U(i:Fin m):=heft (v i); let l:=max h (totalG v); have hp:l≥h:= le_max_left ..; have hu:AppointedH140Through l U:=fun i=> (guardT v i).trans (le_max_right ..); let hv: InCaps U v:= fun _=> le_rfl; let d: AppointedH140Through l (Output h):=fun _=>hp
 let w:=loadScan v hv; rw [onto N H _ d hu v hv]; let Q:=rawCoeff A d hu (forest (0:Points 1) y) k; let R0:= response Q w; have ht(a:Sec G h): R0 a= Q (fun _=>a) w:=response_apply ..
 have hx(i: Toon G h): R0 (theory i)= coeff k (lonelyG Ω y (Dframe.flash i) v):= (ht _).trans (rawCoeff_on_scan A
    (H.separatedOPE 0).wilson.dimensions d hu (Single (Dframe.flash i)) v (fun _=>size_le i) hv _ k)
 simp_rw [← hx]; change _= Q _ w; rw [← show R0 (Normalize.leaf G h)= Q (Λ h) w from ht _]
 calc _ = R0 (∑ i: Toon G h, coord i (Normalize.leaf G h) • theory i) := by simp only [map_sum, _root_.map_smul, smul_eq_mul];
      _ = _:= congrArg R0 (all_sig _)
lemma free_price (x:Points 0)(u:AppointedH140Inputs G (space h)): Served N u x (vacancy h) p h:= by
 intro m S v hS hV; refine carry ?_ (ChargeP.unit); filter_upwards with t y
 rw [furniture N H]; apply Eq.symm; rw [porch_units N H (Λ h) leave (0:Points 1) (squeeze (-t) y.val) (fun _ _=>rfl)
    (lives _ (hV y.property))]; exact sub_eq_zero.mpr (by congr <;> apply Subsingleton.elim)
omit H in
private lemma confVac (x:Points 0):x∈conf 0:= fun i=>Fin.elim0 i
lemma free_order {d:Fin 0→ℕ}(x:Points 0)(u:AppointedH140Inputs G d)(b: Toon G h) : ope A u x (Dframe.flash b) = PowerSeries.C (coord b (Normalize.leaf G h)):=by
 obtain hc:d=space h:=Subsingleton.elim _ _; subst d; rw [← vacancy_flash]
 ext1 k; exact (represents N H u (confVac _) (free_price N H x u (p:=k+1)) (Dframe.flash b) (size_le b) (Nat.lt_succ_self k)).symm
local notation "Y∗"=> PowerSeries.C
-- thus c(H) of all-unit Near always exactly the true unit. the second inequality is exact.
variable {d: Fin n→ℕ}(u:AppointedH140Inputs G d) (hx:∀ i,u i=Normalize.leaf G (d i))
include hx
lemma uninhabited (x:Points n)(hp:x∈conf n)(z:ℝ): croppedVector A h k u x z=Normalize.leaf G h:=by
 rw [proper_vector N H u hp leave (fun i _=> hx i) z]
 have he(f:ℂ): appointedH140Crop k z (Y∗ f)= f:= by rw [crop_eq, Finset.sum_eq_single 0]; simp; exacts [fun i _ hi=> by rw [coeff_C,if_neg hi,mul_zero],by simp]
 unfold croppedVector; simp_rw [free_order N H,he]; exact all_sig _
omit hx H in
lemma duplicateVac {e d:Fin 0→ℕ}{v:AppointedH140Inputs G e}{u:AppointedH140Inputs G d}{g:Fin m→ℕ}(w:AppointedH140Inputs G g)(hd:AppointedH140Through l d)(hv:AppointedH140Through l e)(hg:AppointedH140Through l g)(y:Points m)(ν η:ℝ)(x x':Points 0) :
    let L:= GroupS.gaugeN N.scheme N.criterion Z ν
    fullSeries A L η hd hg x y u w=fullSeries A L η hv hg x' y v w:= by obtain he : d=e:=Subsingleton.elim _ _; subst e; obtain hv:u=v:= Subsingleton.elim _ _; subst v; rw [Subsingleton.elim x x']
lemma vacant_residual {e:Fin m→ℕ}(hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l)(x:Points n)(y:Points m) (w:AppointedH140Inputs G e) (hy:y∈ Outside m)(ν η z:ℝ)(hv:forest x (squeeze η y) ∈ conf (n+m)) :
    difference A (GroupS.gaugeN N.scheme N.criterion Z ν) η hd he hh x y u w p z=0:= by
 let Q := Embedding.refl (Fin m); have ht : keptPoints Q y=y:= by ext;rfl
 have hp : x∈conf n:= fun i j hij=> Fin.castAdd_injective _ _ (hv (a₁:=Fin.castAdd m i) (a₂:=Fin.castAdd m j) (by rw [forest_left,forest_left]; exact hij)) -- hv : Injective
 unfold difference; rw [uninhabited N H u hx x hp z,croppedResponse_apply, replacementSeries]
 rw [sub_eq_zero]; apply congrArg; rw [full_unit_drop N Z H ν hd he leave Q η x y hv u w (fun i _=>hx i) (fun i hi=> False.elim (hi ⟨i,rfl⟩)),full_unit_drop N Z H ν
    (d:=Output h) (fun _=>hh) he leave Q η 0 y (lives _ hy) (fun _=>Normalize.leaf G h) w (fun _ _=>rfl) (fun i hi=> False.elim (hi ⟨i,rfl⟩))]; exact duplicateVac ..
end YM.FVA2.GradedFar.Loft
