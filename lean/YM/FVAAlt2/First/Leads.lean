import YM.FVAAlt2.First.Conv
import YM.FVAAlt2.Convert.Upright
/-!
# Pert.Full forecast arrays.D.Initial. Orientation.P via same Gram system. Full limiting law,
independent of aperture beyond holder q. This is needed ONLY for checking contribution Peal (firstPS). 
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVAAlt2.Home.Subsidy
open Function Set Filter Finset Topology Lattice
open Precision Extra.FD Maxwell Labels Extraction
open FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open MS MS.Menus MS.Book MS.Koszul MS.Book.Program MS.Local.Physical MS.Land MS.Plane MS.Theater
open Subspace Profiles Pairing Report Convert
open Pert
open PowerSeries (C coeff constantCoeff)
open scoped ContDiff BigOperators Topology PowerSeries Classical Matrix
variable {G:Gauge}{F:Frames G}{B: Deck G}{Q:Type}{m r n d:ℕ} {q:Side}
local notation "A"=> PowerSeries ℝ
local notation "CZ"=> PowerSeries ℂ
local notation "Ω"=> constantCoeff (R:=ℝ)
variable (q n)(μ:ℝ) (P: RG10.Position.Plan F)(hP:P.liftOff=LoftPP F)
local notation "Y"=> seats P.liftOff P.certified
local notation "g"=> Glyph Y d
local notation "J"=>RG10.Position.Deck F d
local notation "τ"=> μ- Θ q n
variable {M:MS.Land.Booked (seats P.liftOff P.certified)}(S:MS_Data G M)(V: MS.Land.Prescription (seats P.liftOff P.certified))
local notation "O"=> Lobby.owner
local notation "σ"=> Lobby.redo V.team τ
local notation "W"=> frameO F Y q n μ V d
local notation "SZ"=> revise V.team τ
variable (F)
def plunge (d:ℕ): Datum (RG10.Position.Deck F d)→A:= takeReal∘ bareDeck F n q
variable {F}
def employ (d:ℕ): Datum (RG10.Position.Deck F d)→A:= mix (PowerSeries.subst SZ ∘ plunge F n q d) ( frameO F Y q n μ V d )
variable {D:ChartRatio G}(hD:LocalRatio D)(hg:G.Simple)(hx:TaylorOKPl S (ExtraBook (seats P.liftOff P.certified)) V)(hq:1<q.val)
include hP hg hD hq hx in
lemma measured_p (v:Datum J): AlignSeries atTop (fun m=> employ m q μ P V d v) (science μ S F d v):=by
 let Y₀ (p:Datum g)(i:ℕ):= takeReal ( castF μ V (O ∘ p.2) p.1.test q i ); change AlignSeries atTop _ (mix (currentM μ S) ((dout F Y d).map C) v)
 have he:= (show AlignSeries _ (fun m:ℕ=> mix (fun x=> Y₀ x m) ((dout F Y d).map C) v) _ from move_limit ((dout F Y d).map C) (h:=fun x=> Subspace.costOrder μ hD V S (O ∘ x.2) hg hq hx x.fst.test (nativeR P)) v)
 rw [ show (fun m:ℕ=> employ m q μ P V d v)=_ from funext (fun m=> (congr_fun (roundtrip (n:=m) (q:=q) μ P hP V) v).symm) ]; exact he
-- base cost.Start. compare to Fund not deriving formula from Plan.starts
include hq
open PertExtension.Position.Triangle
lemma start_cost (p:Datum J): Tendsto (fun n=> Ω ( plunge F n q d p )) atTop (𝓝 ( Physical.free (L:=Maxwell.standard F) (RG10.Position.deck F d) p )) := by
 rw [ Report.freeσ F p ];
 let S:= RG10.Position.deck F d; let s:=p.snd; let a:=p.fst
 obtain he:= Rig.zerothProfile d F q hq (S ∘ s) a.test a.test.continuous a.test.hasCompactSupport a.test.tsupport_subset;
 have ht : (fun n=>Ω ( plunge F n q d p ))=fun n:ℕ=>(coeff 0 ( bareDeck F n q p )).re:= by funext n; rw [ ← PowerSeries.coeff_zero_eq_constantCoeff_apply,plunge,Function.comp_apply,takeReal,PowerSeries.coeff_mk ]
 rw [ht]; unfold Report.wickY; have hh(x:Points a.n): Ward.disc (fun j=> (Sigma.mk d ((S∘s) j) : (freeTable F).Tag)) x= Report.wickB F S s x:= by unfold Ward.disc; rw [ Extra.FD.writes_eval ];rfl
 simp_rw [ hh ] at he; exact Complex.continuous_re.continuousAt.tendsto.comp he
-- slope transfer leading by earlier template exactly with different Ax uses (plunge).

local notation "b"=> (din F Y d)
local notation "cL"=> (dout F Y d)
local notation "Yd"=> RG10.Position.Deck F
local notation "X"=> Glyph Y
open Matrix
abbrev Ax (n:ℕ) (d:ℕ) : Datum (Glyph Y d)→ℝ:= mix (Ω ∘ plunge F n q d) (din F Y d)
local notation "cost"=> constantCoeff ∘ (currentM (d:=d) μ S)
omit hq
lemma matched(n:ℕ): mix (Ω ∘ employ n q μ P V d) b=mix (Ax q P n d) (beam0 V ((μ-Θ q n)) (epsilon q n) d):=by
 unfold employ Ax; rw [mixPap,mix2,mix2,map_element, ← Matrix.mul_assoc cL, ← Matrix.mul_assoc,← Matrix.mul_assoc, din_mul F Y, one_mul]; congr! 1; funext x; exact Triangle.substitutes_zero (revise_zer ..) -- order?
include hq
lemma spin_star(v: Datum (X d)): Tendsto (fun n=> Ax q P n d v) atTop (𝓝 (cost v)):=by
 rw [oldStar F]; unfold Ax mix; refine tendsto_finsetSum _ fun i _=>?_ ; exact (start_cost q hq _).mul_const _
include hP hD hg hx
lemma spin_go(v:Datum (X d)): Tendsto (fun n=>mix (Ax q P n d) (beam0 V ((μ-Θ q n)) (epsilon q n) d) v) atTop (𝓝 (cost v)):=by
 simp_rw [← matched]; rw [oldStar F]; unfold mix; apply tendsto_finsetSum _; intro i _; let u:Datum (Yd d) := ⟨ v.fst,i ⟩; let P0(n:ℕ):= (employ n q μ P V d u); let C:=science μ S F d u; change Tendsto (fun n=> Ω (P0 n)*_) _ _; rw [show freeJ F d u = Ω C from (physics F μ S _).symm]; exact ( (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using! measured_p q μ P hP S V hD hg hx hq u 0) : Tendsto (fun n=>Ω ( P0 n )) atTop (𝓝 (Ω C)) ).mul_const _
-- saturated. Induct strong using Witness h and Matrix.limit stability
include μ
lemma clearly(d:ℕ)(x a:ℝ): beam0 V x a d=1:=by
 let X'(m:ℕ):= beam0 V ((μ-Θ q m)) (epsilon q m) d; let H(v j:X d):= Glyph.grade v ≤ Glyph.grade j
 obtain ⟨t,ht⟩:= fulldet F S μ d; let W₁:=layerP t (R:=ℝ) (constantCoeff ∘ currentM (d:=d) μ S); let wp(n:ℕ):= layerP t (Ax q P n d);
 suffices he: ∀ l:ℕ,∀ i:X d,i.grade=l→∀ (y z:ℝ) j, beam0 V y z d i j=(1:Matrix (X d) _ ℝ) i j from Matrix.ext fun i=>he _ i rfl x a;
 intro l; induction l using Nat.strong_induction_on with
 | h l ih=>
   intro i hi; have hv:∀ n j,H i j→( X' n - 1 ) i j=0:=fun n j ht=> sub_eq_zero.mpr (light0 V _ _ _ _ ht)
   have h : Tendsto wp atTop (𝓝 W₁):= tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mpr fun j=> spin_star q μ P S hq (qr t i j)) -- order
   have he: Tendsto (fun j=> X' j * wp j * ( X' j )ᵀ ) atTop (𝓝 W₁):=by
      let h(k:ℕ):= X' k * wp k * (X' k)ᵀ; rw [ show (fun j:ℕ=> _)= (fun i=> layerP t (mix (Ax q P i d) (X' i))) from funext fun i=>(swatch t _ ( X' i )).symm ]; exact tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> spin_go q μ P hP S V hD hg hx hq (qr t i j) -- args
   have hN:Tendsto (fun j=> (X' j-1) i) atTop (𝓝 0):= nested Glyph.grade W₁ i ht (fun v j hv hj=> white F S μ t v j ( Nat.ne_of_lt (hv.trans_le hj) )) hv (fun n j hx' k=> ih _ (hx'.trans_eq hi) j rfl _ _ k) h he
   intro y z j; by_cases hx:H i j; · exact light0 V _ _ _ _ hx
   have h':i≠j:=fun e=> hx (by rw [← e])
   rw [Matrix.one_apply_ne h']; apply rigidity V q μ hq; apply Filter.Tendsto.congr (fun k=>?_) (tendsto_pi_nhds.mp hN j); rw [Matrix.sub_apply,Matrix.one_apply_ne h',sub_zero]
-- ∀ θ on q=1 degenerately not needed; ∀ actual profile.NEXT.Field.
lemma ready(d n:ℕ): (frameO F Y q n μ V d).map Ω=1:=by rw [map_element,clearly q μ P hP S V hD hg hx hq d,Matrix.one_mul,dout_mul]
end YM.FVAAlt2.Home.Subsidy
