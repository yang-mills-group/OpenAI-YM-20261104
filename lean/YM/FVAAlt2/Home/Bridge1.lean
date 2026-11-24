import YM.FVAAlt2.Home.Wake
/-! The lead PS frame is **exactly** identity. This uses triangularity in
 slot count and nontrivial Wick Gram, no pre-assumed convergence of frame entries.
 `employed` thus computed on **precisely** the same near-free leading regulated data as beginsAt.
 Positive order commuting and unit proofs remain separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Report
open Function Filter Set Finset Topology Lattice
open Precision Extra.FD Maxwell Labels Extraction
open FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open MS MS.Local.Physical MS.Koszul MS.Menus MS.Book MS.Plane MS.Theater MS.Land
open MeasureTheory Matrix
open PowerSeries (C coeff constantCoeff)
open Profiles
open RG10.Position (Plan)
open scoped Topology BigOperators ContDiff PowerSeries Classical Matrix
variable {G: Gauge} {L:Labels.Frames G}{d:ℕ} {H:Source.Hol G}
variable (P:Plan L)(D: ChartRatio G){M:Booked (seats P.liftOff P.certified)}(S:MS_Data G M)(q:ℕ+)(μ:ℝ)(K:Prescription (seats P.liftOff P.certified))
local notation "F"=> seats P.liftOff P.certified
local notation "X"=> Glyph F
local notation "Y"=> RG10.Position.Deck L
local notation "τ" n=> μ- Θ q n
local notation "Ω"=> constantCoeff (R:=ℝ)
local notation "b"=> (din L F d)
local notation "c"=> (dout L F d)
set_option linter.unusedSectionVars false
lemma map_element(n:ℕ): (frameO L F q n μ K d).map Ω=c * ( beam0 K (τ n) (epsilon q n) d*b ):= by rw [frameO, Matrix.map_mul, Matrix.map_mul]; rfl
abbrev Ax (n:ℕ) (d:ℕ) : Datum (Glyph F d)→ℝ:= mix (Ω ∘ P.begins q n d) (din L F d)
local notation "cost"=> constantCoeff ∘ (currentM (d:=d) μ S)
lemma matched(n:ℕ): mix (Ω ∘ employed P q n μ K d) b=mix (Ax P q n d) (beam0 K (τ n) (epsilon q n) d):=by
 unfold employed Ax; rw [mixSame,mixPap,mix2,mix2,map_element, ← Matrix.mul_assoc c, ← Matrix.mul_assoc,← Matrix.mul_assoc, din_mul L F, one_mul]; congr! 1; funext x; exact Triangle.substitutes_zero (revise_zer ..) -- order?
variable (hP:LocalRatio D)(hq:1<q.val)(hg:G.Simple)(hX:TaylorOKPl S (Lobby.Table (nativeR P) (seats P.liftOff P.certified)) K)
include hq

lemma spin_star(v: Datum (X d)): Tendsto (fun n=> Ax P q n d v) atTop (𝓝 (cost v)):=by
 rw [oldStar L]; unfold Ax mix; refine tendsto_finsetSum _ fun i _=>?_ ; exact (RG10.Position.Plan.starts hq P _).mul_const _
include hg hP hX
lemma spin_go(v:Datum (X d)): Tendsto (fun n=>mix (Ax P q n d) (beam0 K (τ n) (epsilon q n) d) v) atTop (𝓝 (cost v)):=by
 simp_rw [← matched]; rw [oldStar L]; unfold mix; apply tendsto_finsetSum _; intro i _; let u:Datum (Y d) := ⟨ v.fst,i ⟩; let P0(n:ℕ):= (employed P q n μ K d u); let C:=science μ S L d u; change Tendsto (fun n=> Ω (P0 n)*_) _ _; rw [show freeJ L d u = Ω C from (physics L μ S _).symm]; exact ( (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using! measured P D q μ S K u hP hg hX hq 0) : Tendsto (fun n=>Ω ( P0 n )) atTop (𝓝 (Ω C)) ).mul_const _
-- saturated. Induct strong using Witness h and Matrix.limit stability
include μ
lemma clearly(d:ℕ)(x a:ℝ): beam0 K x a d=1:=by
 let X'(m:ℕ):= beam0 K (τ m) (epsilon q m) d; let H(v j:X d):= Glyph.grade v ≤ Glyph.grade j
 obtain ⟨t,ht⟩:= fulldet L S μ d; let W:=layerP t (R:=ℝ) (constantCoeff ∘ currentM (d:=d) μ S); let g(n:ℕ):= layerP t (Ax P q n d);
 suffices he: ∀ l:ℕ,∀ i:X d,i.grade=l→∀ (y z:ℝ) j, beam0 K y z d i j=(1:Matrix (X d) _ ℝ) i j from Matrix.ext fun i=>he _ i rfl x a;
 intro l; induction l using Nat.strong_induction_on with
 | h l ih=>
   intro i hi; have hv:∀ n j,H i j→( X' n - 1 ) i j=0:=fun n j ht=> sub_eq_zero.mpr (light0 K _ _ _ _ ht)
   have h : Tendsto g atTop (𝓝 W):= tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr fun j=> spin_star P S q μ hq (qr t i j)) -- order
   have he: Tendsto (fun j=> X' j * g j * ( X' j )ᵀ ) atTop (𝓝 W):=by
      let h(k:ℕ):= X' k * g k * (X' k)ᵀ; rw [ show (fun j:ℕ=> _)= (fun i=> layerP t (mix (Ax P q i d) (X' i))) from funext fun i=>(swatch t _ ( X' i )).symm ]; exact tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> spin_go P D S q μ K hP hq hg hX (qr t i j) -- args
   have hN:Tendsto (fun j=> (X' j-1) i) atTop (𝓝 0):= nested Glyph.grade W i ht (fun v j hv hj=> white L S μ t v j ( Nat.ne_of_lt (hv.trans_le hj) )) hv (fun n j hx' k=> ih _ (hx'.trans_eq hi) j rfl _ _ k) h he
   intro y z j; by_cases hx:H i j; · exact light0 K _ _ _ _ hx
   have h':i≠j:=fun e=> hx (by rw [← e])
   rw [Matrix.one_apply_ne h']; apply rigidity K q μ hq; apply Filter.Tendsto.congr (fun k=>?_) (tendsto_pi_nhds.mp hN j); rw [Matrix.sub_apply,Matrix.one_apply_ne h',sub_zero]
-- ∀ θ on q=1 degenerately not needed; ∀ actual profile.NEXT.Field.
lemma ready(d n:ℕ): (frameO L F q n μ K d).map Ω=1:=by rw [map_element,clearly P D S q μ K hP hq hg hX d,Matrix.one_mul,dout_mul]
end YM.FVAAlt2.Home.Report
