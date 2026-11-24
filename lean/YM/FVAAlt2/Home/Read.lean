import YM.FVAAlt2.Home.Shine
/-! Smearing the arrays in the precise $Y∧O input manifest. Estimate for
Wilson-to-MS *profiles*, unit Region.Points, using Grid (of RG10.C*).
Error not subsequently multiplied by diverging field matrices. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Profiles
open Function Set Filter Finset Lattice Topology Metric
open FormalOPE RG10.InversionTop
open PertExtension PertExtension.LatticePT PertExtension.LatticePT.Mixed PertExtension.Position
open Extraction Precision
open MeasureTheory MS MS.Koszul MS.Menus MS.Book MS.Tone MS.Vista MS.Tide
open PowerSeries (C coeff)
open scoped Topology BigOperators ContDiff PowerSeries
variable {G:Gauge}{L:Labels.Frames G} {H:Source.Hol G}{B: MS.Local.Physical.Deck G}{M:MS.Land.Booked B}{d:ℕ}
variable (D: ChartRatio G)(R:Lobby.Registry L H)(S:MS.Land.MS_Data G M)(P:MS.Land.Prescription B)(p:Fin d→ Rake.Label B)
variable (μ:ℝ){q:ℕ+}(hp:LocalRatio D)(h:1<q.val)(hg:G.Simple)(hc:MS.Land.TaylorOKPl S (Lobby.Table R B) P) {Ψ: Test d}
abbrev area (k:ℕ)(x:Points d):ℂ:= Dial.tour S p μ (realize x) Finset.univ k
variable {x:Points d}(o:(i:ℕ)→Native q i)(he:∀ i,o i∈ origins q i)
set_option linter.unusedSectionVars false
include h he hp hg hc
lemma reaches (k:ℕ)(hx:x∈ conf d)(u:(i:ℕ)→Grid.offsets q d i)(hy:Tendsto (fun i=> Grid.sample q i (u i)) atTop (𝓝 x)):
   Tendsto (fun i=>pixelT μ D R P q i k p (u i) (o i)) atTop (𝓝 (area S p μ k x)):= by
 obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp ((conf_open d).mem_nhds hx); let K:= Metric.closedBall x (r/2); have hh:0<r/2:= half_pos hr
 let Y(k:ℕ):=Grid.sample q k (u k); let f(i:ℕ):= pixelT μ D R P q i k p (u i) (o i); let w(i:ℕ):= area S p μ k ( Y i )
 obtain ⟨C,hC,T⟩:= reception μ D R S P p hp hc hg (show IsCompact K from isCompact_closedBall ..) (show K⊆conf d from (Metric.closedBall_subset_ball (half_lt_self hr)).trans hR) h k
 have hl:Tendsto w atTop (𝓝 (area S p μ k x)):= (Dial.contin S p _ (realize_one hx) _ _ μ |>.1 ).tendsto.comp (realize_s.continuousAt.tendsto.comp hy)
 have hz : PeakT atTop { θ:= Θ q,η:=0,room:=theta_nonneg q } mildG (f-w):= ⟨C,hC,( T.and (hy.eventually (Metric.closedBall_mem_nhds x hh)) ).mono fun i hh=> hh.1 _ hh.2 _ (he i) ⟩
 have hu:= (PeakT.topos mild_p (grows h) hz).add hl; rw [zero_add] at hu; exact (by change Tendsto f _ _; rw [← sub_add_cancel f w]; exact hu) -- f appears RHS? see
omit he o
-- infer real-valued readings at physical points FROM exact reference matching
lemma area_jet (hx:x∈conf d)(k:ℕ): (↑((area S p μ k x).re):ℂ)=area S p μ k x:= by
 choose s hs using (hasOrigin q); let A(i:ℕ):= Grid.signal q i x
 have hz := reaches D R S P p μ hp h hg hc s hs k hx A (Grid.choose_sample h x)
 have hh(t:ℕ): pixelT μ D R P q t k p (A t) (s t)= (↑(pixelT μ D R P q t k p (A t) (s t)).re:ℂ):= Eq.symm (coinPixel R D p μ P q t k ..) -- check args
 exact tendsto_nhds_unique ((Complex.continuous_ofReal.continuousAt.tendsto.comp (Complex.continuous_re.continuousAt.tendsto.comp hz)).congr (fun i=> (hh i).symm)) hz

variable (φ:Points d→ℝ){K:Set (Points d)}(hK:IsCompact K)(hx:K⊆conf d)(hf:support φ⊆K)(hw:Continuous φ)
local notation "E" i t=> epsilon i t
-- per origin readings ($W numeric, getting ALL footprint points of the profile class).
local notation "f!"=> pixelT μ D R P
private def arithmetic (p:Fin d→ Rake.Label B)(k:ℕ): ℕ→ ℝ:=fun i=>epsilon q i^(4*d)*∑ x:Grid.offsets q d i, φ (Grid.sample q i x) * (pixelT μ D R P q i k p x (o i)).re
include hK hx hf hw
include o he
lemma earns (k:ℕ): Integrable (fun x=>φ x*(area S p μ k x).re) ∧ Tendsto (arithmetic D R P μ o φ p k) atTop (𝓝 (∫ x, φ x*(area S p μ k x).re)):= by
 have hm(x:Points d)(hx:x ∉ K): φ x=0:= notMem_support.mp (fun H=> hx (hf H))
 exact Grid.integrable_spots h (fun v x hx' ht=> (hw.continuousAt.tendsto.comp ht).mul (Complex.continuous_re.continuousAt.tendsto.comp (reaches D R S P p μ hp h hg hc o he k (hx hx') v ht))) hK (fun i x hx=> by rw [hm _ hx, zero_mul]) (fun _ hx=>by rw [hm _ hx,zero_mul])

omit he o hx hK hw hf hp hg hc h
-- prices right-hand Cost before coupling normalization coordinate. choose real Φ; wrap to complex moment by extension.
def YReport(q:ℕ+)(m:ℕ):= visit q m (φ ∘ points) (fun x:Fin d→ Native q m => Lobby.newEra D R P (μ-Θ q m) p x (epsilon q m))
abbrev forecast (S:MS.Land.MS_Data G M)(p:Fin d→Rake.Label B)(μ:ℝ)(φ:Points d→ℝ) : PowerSeries ℝ:= PowerSeries.mk (fun k=>∫ x, φ x*(area S p μ k x).re)
lemma actualBill (q:ℕ+)(n:ℕ): RSpec (YReport D R P p μ φ q n):=by unfold YReport visit; exact RSpec.finSum _ fun i _=> RSpec.finSum _ fun k _=> (RSpec.constants _).mul ( realP R D p _ _ P _) -- arguments
lemma bill_t(k:ℕ)(q:ℕ+)(m:ℕ): coeff k (takeReal (YReport D R P p μ φ q m))=((origins q m).card:ℝ)⁻¹ * ∑ i∈ origins q m,epsilon q m^(4*d)* ∑ x:Grid.offsets q d m,φ (Grid.sample q m x)*(f! q m k p x i).re:=by
 unfold takeReal YReport visit; simp_rw [PowerSeries.coeff_mk,map_sum,Complex.re_sum,Finset.mul_sum]; rw [Finset.sum_comm]; refine sum_congr rfl fun i _=> sum_congr ?_ fun j hj=>?_; rotate_left
 · rw [PowerSeries.coeff_C_mul,Mixed.price,Grid.sample_eq]; simp only [Function.comp_apply,Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,zero_mul,sub_zero,pixelT,Fintype.card_fin]; ring
 congr
include hx hK hw hf hp hg hc h
lemma goes : AlignSeries atTop (fun v=>takeReal (YReport D R P p μ φ q v)) (forecast S p μ φ):= by
 intro i; simp_rw [forecast,PowerSeries.coeff_mk,bill_t]; apply Grid.average_paths ( hn:=fun _=> hasOrigin q _ ); exact fun k hk=> (earns D R S P p μ hp h hg hc k hk φ hK hx hf hw i).2
-- more germ uniform profile scopes later
end YM.FVAAlt2.Home.Profiles
