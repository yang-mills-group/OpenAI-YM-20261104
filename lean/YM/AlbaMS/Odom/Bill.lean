import YM.AlbaMS.Odom.Nomad

/-!
# Lattice perturbative standard book, except polar geometry

Works also on based or pin constraints. Use whenever account by Receipts.
Frames independent of stencil locations & horizons so far. All-order tuning
used only after establishing for each horizon, no estimates on value of a
resummed coupling. Laplace-Wick definition still needs lattice gauge choice.
`capital` contains the overall accounting (real powers). Film only when value
&, no Laurent inversions nil. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Odom
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil Inlay Inlay.Net Lattice
variable {G:Gauge} {V I W J R L : Type*}[Fintype V][Fintype W][Fintype I][Fintype J]{Ω:Net V I}{H:Net W J}
/-- actual bosonic integrand on links, chart for producing measure germs,
value/slope at origin. Used on quotient before/after rescaling too. -/
structure Book (Ω:Net V I)(G:Gauge) extends Luster Ω G where
  patch : Precision.ChartRatio G
  paid : Precision.LocalRatio patch
  val0 : toLuster.caseG.val 0=0
  slope : fderiv ℝ toLuster.caseG.val 0=0
namespace Book
variable (F:Book Ω G)[CommRing R](T:Tune R){a:ℝ}
-- this book uses one mesh and these determinants already checked relative to G.
def main : Heave G V I ℝ:=superb (grit _ I) Ω.chat (bare F.toLuster.caseG)
def ash : Heave G V I ℝ:=bare (fragrant F.paid)
def charter : Heave G V I R:= T.fuelT F.main F.ash
def first (a:ℝ)(ha:0<a):= Tune.kinetic a ha F.main
def fair : Heave G V I R:= Wind ø T.D (F.first T.a T.ha)
def stim : Heave G V I R:= F.charter T-F.fair T
-- Interaction not rank homogenized. fully accounted.
theorem trust : Trad F.main F.ash (Loft.oriented ℝ) Finset.univ:= (F.toLuster.panel F.paid).keep (state F.val0 F.slope)
theorem charter_cap (h:IsNilpotent T.z) : FinRank (F.charter T):= (T.bounded h).sub (T.bounded h)
theorem charter_quiet (ha:0<a): F.charter (Tune.baseT a ha)=F.first a ha:= Tune.fuel_base ha F.trust.grow (needy.empty (scent_zero (V:=V) F.paid))
theorem fair_rank : Heg 2 (F.fair T) := (Tune.two_k T.ha).seep _ _
theorem charter_tone : EvenT (F.charter T):= (T.excited F.trust.tone).sub (T.excited F.trust.dossier)
theorem fair_tone : EvenT (F.fair T):= by unfold fair; rw [← F.charter_quiet T.ha]; exact (F.charter_tone _).seep _ _ _
theorem stim_rank (h:IsNilpotent T.z) : FinRank (F.stim T):= (F.charter_cap T h).sub ⟨_,(F.fair_rank T).cap _ _⟩
theorem stim_tone : EvenT (F.stim T):= (F.charter_tone _).sub (F.fair_tone _)
theorem charter_shift (c:G.Color)(h:Runs Ω):
    Net.air (fun i=>T.D (fill c i)) (F.charter T)= (T.D (T.a^4) * T.coul) • Wind ø T.D (hill c):= T.shiftT c h _ (bare_simple (V:=V) _).2
lemma fair_shift (c:G.Color)(h:Runs Ω): Net.air (fun i=>T.D (fill c i)) (F.fair T)=0:=by unfold fair; rw [← charter_quiet,← air_move,show air (fill c) (F.charter _) = _ from F.charter_shift (Tune.baseT T.a T.ha) c h]; unfold Tune.baseT Tune.coul; simp -- fix
lemma stim_shift (c:G.Color)(h:Runs Ω): Net.air (fun i=>T.D (fill c i)) (F.stim T)= (T.D (T.a^4)*T.coul) • Wind ø T.D (hill c):=by rw [stim,map_sub,F.charter_shift T c h,F.fair_shift T c h,sub_zero]
variable [Algebra ℚ R]
theorem lodging : master T.bracket Finset.univ (F.charter T)=0:= T.liftT F.trust
omit [Fintype V] [Fintype I] [Algebra ℚ R] in
private lemma base_br (i j:Leaf G V I): T.bracket i j=T.D ((Tune.baseT T.a T.ha).bracket i j):=by
  rcases i with (i|i)|(i|i)<;> simp only [Tune.bracket,Tune.baseT,Loft.oriented,RingHom.id_apply] <;> first|(split <;> simp only [map_mul,map_pow,map_neg,map_zero,map_one])| (simp only [map_mul,map_pow,map_zero]) -- fix
lemma fair_master : master T.bracket Finset.univ (F.fair T)=0:=by
  unfold fair; rw [← charter_quiet,master];
  have h : T.bracket=fun i j : Leaf G V I=> T.D ((Tune.baseT T.a T.ha).bracket i j):= funext fun _=> funext fun _=> base_br ..; rw [h, ← Wind_cross, ← Wind_touch,← halve_unique T.D, ← Wind_smul, ← map_sub (Wind _ _), show halve ℝ • cross _ _ _ _ _- _=0 from lodging .., map_zero] -- h inference
lemma engine_master : master_eff (tether true T.bracket Finset.univ (F.fair T)) T.bracket Finset.univ (F.stim T)=0:=by
  have he:= F.lodging T; rw [← sub_add_cancel (F.charter T) (F.fair T)] at he; unfold master at he; rw [add_cross,cross_add,cross_add] at he; change halve R • (cross true _ _ _ _+cross true T.bracket Finset.univ (F.stim T) (F.fair T)+(cross true T.bracket Finset.univ (F.fair T) (F.stim T)+_))-_=_ at he; rw [cross_flip (F.stim_tone T) (F.fair_tone T) T.prime] at he; -- cancel compare
  let A:=cross true T.bracket Finset.univ (F.stim T) (F.stim T); let B:=cross true T.bracket Finset.univ (F.fair T) (F.stim T); let C':=cross true T.bracket Finset.univ (F.fair T) (F.fair T); have hh : halve R • C'=touch T.bracket Finset.univ (F.fair T):=sub_eq_zero.mp (F.fair_master T); change halve R • (A+B+(B+C')) - touch _ _ (F.stim T+F.fair T)=0 at he; rw [show A+B+(B+C')=A+(B+B)+C' by abel, smul_add,smul_add,twice_halve,map_add,hh] at he
  unfold master_eff master; rw [from_tether]; change B+(_ • A-touch _ _ _) =_; exact Eq.trans (by abel) he -- sees
end Book
variable (G)(n:Side)
abbrev Rack (P:Precision.ChartRatio G)(hp:Precision.LocalRatio P): Book (deck n) G where
  toLuster:= day G n
  patch:=P
  paid:=hp
  val0:= (front G n).1
  slope:= (front G n).2.1
end YM.MSBar.Odom
