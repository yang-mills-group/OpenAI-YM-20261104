import YM.FVAAlt2.First.Check
/-! Reg.MS orientation action with real part of arbitrary complex test: commute EXACTLY. -/
noncomputable section
set_option autoImplicit false
namespace YM.FVAAlt2.Home.Subsidy
open Function Set Filter Finset Topology Lattice
open Precision Extra.FD Maxwell Labels Extraction
open FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open MS MS.Menus MS.Book MS.Koszul MS.Book.Program MS.Local.Physical MS.Land MS.Plane MS.Theater
open Subspace Profiles Pairing Pert
open PowerSeries (C coeff constantCoeff)
open scoped ContDiff BigOperators Topology PowerSeries Classical Matrix
variable {G:Gauge}{F:Frames G}{B: Deck G}{Q:Type}{E:E4} {m r n d:ℕ} {q:Side}
local notation "A"=> PowerSeries ℝ
local notation "Cℝ"=> PowerSeries ℂ
lemma take_sum {I:Type}(q: Finset I) (f:I→ Cℝ) : takeReal (∑ i∈q,f i)=∑ i∈q,takeReal (f i):=by ext1 k; unfold takeReal; simp only [map_sum,PowerSeries.coeff_mk,Complex.re_sum]
lemma take_mu (p:Cℝ)(a:A): takeReal (p*into a) = takeReal p*a:=by ext1 k; unfold takeReal; simp_rw [PowerSeries.coeff_mk,PowerSeries.coeff_mul,Complex.re_sum,Complex.mul_re,into_coeff]; simp only [Complex.ofReal_im,Complex.ofReal_re,mul_zero,sub_zero,PowerSeries.coeff_mk]
lemma take_redo(t:Team)(y:ℝ)(p:Cℝ): takeReal (Lobby.redo t y p)= PowerSeries.subst (revise t y) (takeReal p):=by
 ext1 k; rw [takeReal,PowerSeries.coeff_mk]; unfold Lobby.redo; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [ PowerSeries.coeff_mk,Program.rules,Complex.re_sum, AlignSeries.subst_finite (p:=revise t y) ( revise_zer .. ) ]; refine Finset.sum_congr (by ext; simp) fun i _=>?_ ; unfold cut Ends.unpack;
 rw [ show Program.shift t y=into (revise t y) from Eq.symm (RSpec.shapes t y), ← map_pow,into_coeff]; simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re, Complex.ofReal_im, zero_mul,sub_zero,takeReal,PowerSeries.coeff_mk]; rw [mul_comm]
lemma take_mix {I J:Type}[Fintype I][Fintype J] (X: Matrix I J (PowerSeries ℝ))(p: Datum J→ Cℝ): takeReal ∘ mix p (X.map into)= mix (takeReal ∘ p) X:= by funext k; unfold mix; simp_rw [Function.comp_apply,take_sum,Matrix.map_apply,← map_prod,take_mu]
-- core rank map profile (using full profile complex; through arbitrary labels.Pos)
local notation "ξ"=> Full.topSpacing
abbrev Rooms (v:Datum Q):= Fin v.1.n
variable (q n)
local notation "L"=>Full.period q n
lemma psmears (f:Test m)(p:Tprod q n (d:=m)→ Cℝ) (a:Cℝ): psmear q n f (fun i=> a*p i)= a* psmear q n f p:= by unfold psmear; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> mul_left_comm ..
lemma psmearL {I:Type} (f:Test m)(p:I→Tprod q n (d:=m)→ Cℝ)(s:Finset I): psmear q n f (fun i=>∑ j∈s,p j i)=∑ j∈s,psmear q n f (p j):= by unfold psmear; simp_rw [Finset.mul_sum]; exact Finset.sum_comm
lemma psmearRed(t:Team)(y:ℝ)(f:Test m)(p:Tprod q n (d:=m)→ Cℝ): Lobby.redo t y (psmear q n f p)= psmear q n f (Lobby.redo t y ∘ p):= by unfold psmear; rw [map_sum]; simp_rw [← PowerSeries.smul_eq_C_mul, map_smul]; rfl
variable (F B)
def bareP (v :Datum (Glyph B d)) : Cℝ:= Full.profile d v.1.n F q n v.fst.test (mast B d F ∘ v.2)
def bareDeck(v: Datum (RG10.Position.Deck F d)): Cℝ:=Full.profile d v.1.n F q n v.fst.test (RG10.Position.deck F d ∘ v.2)
variable {F B}
variable (μ:ℝ) (P: RG10.Position.Plan F)(hP:P.liftOff=LoftPP F)
local notation "Y"=> seats P.liftOff P.certified
local notation "g"=> Glyph Y d
local notation "J"=>RG10.Position.Deck F d
local notation "τ"=> μ- Θ q n
variable (V: MS.Land.Prescription (seats P.liftOff P.certified))
local notation "X"=> aboard V ( epsilon q n ) τ d
local notation "X0"=> Report.beamA V τ ( epsilon q n ) d
local notation "O"=> Lobby.owner
local notation "σ"=> Lobby.redo V.team τ
include hP in
lemma mon_home(v:Datum g): bareP F Y n q v= psmear q n v.fst.test (fun x=> atPaid x (epsilon q n) (Lobby.owner∘ v.2)):=by -- notation εq define
 unfold bareP psmear Full.profile; rw [MultilinearMap.sum_apply]; refine sum_congr rfl fun i _=>?_ ; rw [ MultilinearMap.smul_apply ,PowerSeries.smul_eq_C_mul, ←epsilon_here ]; exact congr_arg ( PowerSeries.C _ * · ) ( row_paid ( ξ _ _ ) P hP _ (Full.sized q n) _ )
include hP in
lemma micro_era : (fun p:Datum g=> castF μ V (O ∘ p.2) p.1.test q n)=mix ( σ ∘ bareP F Y n q ) X:=by
 funext p; obtain ⟨a,k⟩:=p; let U (i:Fin a.n):= Lobby.owner ( k i ); let J' (i:Fin a.n):=Glyph Y ( U i ).h; let H(i:Fin a.n)(j:J' i):g:= up ( high ( k i )) j; symm; rw [monoread a k _ _ H (fun i=> up_inj (high (k i))) ?hp]; swap
 · intro i j hk; unfold aboard; rw [Matrix.of_apply,oilPoint]; exact sum_eq_zero fun k _=> if_neg (fun h=> hk ⟨k,h⟩)
 unfold castF Subspace.earn boardX; rw [epsilon_here, psmearL ]; refine sum_congr rfl fun i _=>?_ ; unfold Function.comp; rw [psmears,mon_home n q P hP ⟨a,(fun k=>_ )⟩, mul_comm _ (∏ _,_),psmearRed ]; refine congr_arg₂ (·*·) ?_ rfl; exact Finset.prod_congr rfl fun k _=> onOil ..
-- transfer deck. general; Basis repr, no in-maturity assumptions.
variable (F B) in
lemma bare_mix : bareP F B n q (d:=d) = mix (bareDeck F n q) (readC F B d):=by
 funext v; unfold bareP bareDeck mix; let M:= Full.profile d v.1.n F q n v.fst.test; let f:= RG10.Position.deck F d; let o(i:Fin v.1.n)(j:RG10.Position.Deck F d):= Ωc F B (v.2 i) j
 change M _= _; rw [show ⇑(mast B d F) ∘ v.2=fun i:Fin v.1.n=> ∑ j:RG10.Position.Deck F d,o i j • f j from funext fun i=> (tally_c F B (v.2 i)).symm,MultilinearMap.map_sum ]; apply Finset.sum_congr rfl; intro i _; rw [MultilinearMap.map_smul_univ]; change (∏ j,o j (i j)) • M _= M _*∏ j, C (o j (i j)); rw [ ← map_prod, PowerSeries.smul_eq_C_mul,mul_comm];rfl
local notation "XA"=> frameO F Y q n μ V d
local notation "SZ"=> revise V.team τ
include hP in
lemma roundtrip : mix (takeReal ∘ fun p:Datum g=> castF μ V (O ∘ p.2) p.1.test q n) ((dout F Y d).map C) = mix (PowerSeries.subst SZ ∘ takeReal ∘ bareDeck F n q ) XA :=by
 rw [micro_era n q μ P hP V,bare_mix F Y n q,redoes, show PowerSeries.subst SZ ∘ takeReal ∘ bareDeck F n q (d:=d) = takeReal ∘ (σ ∘ bareDeck F n q) from funext fun i=> (take_redo ..).symm, ← take_mix, ← take_mix, frame_board, ← θout F Y, mix2, mix2, Matrix.mul_assoc ]
end YM.FVAAlt2.Home.Subsidy
