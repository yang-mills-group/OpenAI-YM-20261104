import YM.FormalBulk08.Primer.Model

noncomputable section
set_option autoImplicit false
/-! ### Formal vacuum solution (worked interface)
For convenience we put `σ(Z)` from `windowBasis`. α≔`targetPower`. No limit budgets at unadmitted E. Field horizon costs & gauge in this and following files. All CTA assembly on the SAME schedule as chosen Family. This interface doesn't change recursor inputs from capacities/horizon; Plaza construction exported later uses SectionData. -/
namespace YM.FormalBulk08.Primer
open Lattice Laurent Bloch RG Precision Wilson Filter Function Set
open scoped Topology BigOperators ENNReal Matrix ContDiff Classical Matrix.Norms.Frobenius
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Gorge Lava Lotus Shore North Quire Elm Borough Spigot Delphi
open Stationary hiding seat Rays
open Aster
open PhysicalNext.Repeat.Legato Next.Foundations
variable {G : Gauge}(C:Family G)(h:G.Simple){u:ℕ→ℕ}
variable (a:hue G)(L: Families C)

abbrev ChamberU (k:ℕ):= First.cbook L k (FamilyWindow C) (lyre C.path.levels)
abbrev indexN {k i:ℕ} (he:k≤ i): Leaf (ChamberU C L k).scrolls := ⟨PUnit.unit,i,he⟩
def vacuumLimit (i:ℕ) : Pot G:= heir a (chart G) (ChamberU C L 0) PUnit.unit i
lemma limit_eq (k i : ℕ): vacuumLimit C a L i=heir a (chart G) (ChamberU C L k) PUnit.unit i:=rfl

section
variable {E e J k i:ℕ}
variable (p:Announced C u)(hJ:5≤J)(hk:J≤ C.path.levels.clock.J (k+1))(hE:E≤J)
include h hJ
-- exposure exists at ANY horizon (incl bottom if initial J already ≥J). Not supplanted by age varying K.
omit hJ h in
lemma always_opens : ∃ k, J ≤ C.path.levels.clock.J (k+1):= by
    obtain ⟨k,hk⟩:= (C.path.levels.fits.deep.eventually (eventually_ge_atTop J)).exists
    exact ⟨k,hk.trans (C.path.levels.fits.mono (Nat.le_succ _))⟩
include p hk
lemma scripted : Poster (Noise C) Spigot.herald C.labels.level C.params (chart G) (ChamberU C L k) J := by
     let W:= (ChamberU C L k); exact presold h (W:=FamilyWindow C) (U:=W.toEmpire) (fun _=>p.power) W.neck hJ (fun _=> hk)
-- quoting stock loglog-aged aperture.
include hE
lemma Culminates (he:e≤E)(r:ℕ) :
     ∃ (c:ℝ)(m:ℕ),0≤c ∧ ∀ i:ℕ,k ≤ i →
         let z:= ageZ (C.path.levels.clock.hatBeta i); let α:= targetPower; let v:= (FamilyWindow C).width (C.path.levels.clock.J i)
         let S:= fun n=> densityCoeff C L a n i e r
         let T:= vacuumLimit C a L i e r
         Boone S T ∧ Bail (fame _) v T (c*z^m) ∧
            ∀ N≥i, Bail (fame _) v (S N-T) (c*z^m*ratioR C.S N i α) := by
      let W:= ChamberU C L k; have hp : Poster (Noise C) Spigot.herald C.labels.level C.params (chart G) W J := scripted C h L p hJ hk
      obtain ⟨B,⟨c,m,hc,T⟩,V,Y⟩:= diadem a (hp.vac _ hE) (chart_ok G) h he r
      refine ⟨c,m,hc,fun i hi=>?_⟩; intro z y v S R; let x:= indexN C L hi; have hv:B x≤ c*z^m:= by
          have he:(chron _|>.day x)=z := Borough.measure p.power i
          rw [←he]; exact (le_abs_self _).trans (T x)
      exact ⟨North.crown a (hp.vac _ hE) (chart_ok G) h he r x,(Y x).1.mono hv,fun N hn=>((Y x).2 N hn).mono (mul_le_mul_of_nonneg_right hv (ratioR_pos ..).le)⟩
-- ***NOT*** hypothesizing provenance from this stability
lemma modulus (he:e ≤ E)(r:ℕ) : ∃ c m, (0:ℝ) ≤ c ∧ ∀ i:ℕ,k ≤ i →∀ N≥ i, ∀ M≥N,
      let z:= ageZ (C.path.levels.clock.hatBeta i); let T:=fun N=>densityCoeff C L a N i e r; let v:= (FamilyWindow C).width (C.path.levels.clock.J i)
      Bail (fame _) v (T N) (c*z^(m:ℕ)) ∧ Bail (fame _) v (T N - T M) (c*z^m* ratioR C.S N i targetPower) := by
   let W:= ChamberU C L k; have hp:= scripted C h L p hJ hk
   obtain ⟨B,⟨c,m,H,S⟩,X,Y⟩:= tenuous a (hp.vac E hE) (chart_ok G) h he r
   refine ⟨c,m,H,fun i hi N hn M hm=>?_⟩; intro z T v; let x:= indexN C L hi
   have hs : B x ≤ c*z^m:= by rw [← show (chron _|>.day x)=z from Borough.measure p.power i]; exact (le_abs_self _).trans (S x)
   exact ⟨(Y x N M hn hm).1.mono hs,(Y x N M hn hm).2.mono (mul_le_mul_of_nonneg_right hs (ratioR_pos ..).le)⟩
lemma remains (x:k≤ i)(he:e≤E):
     let T:= vacuumLimit C a L
     T i e = Wine.normalized a (crest (chart G) a (indexN C L x) (T (i+1))) e ∧ (∀ n, Charter (stone (T i) n) E) ∧
       (0<e → Cork.Null ((T i) e 2)) ∧ ∀ b:hue G,Cork.value b ((T i) 0 2)=1 := by
    intro T; let z:= indexN C L x; have ht:=(scripted C h L p hJ hk).vac _ hE
    exact ⟨continuation a ht (chart_ok G) h z he,fun n=>clamps a ht (chart_ok G) h z n,limited_seal a ht (chart_ok G) h z he,capital a ht (chart_ok G) h z⟩

-- Trace readers fixed here from derivative d² and transverse polish.
open PowerSeries
lemma normalized_shift :
    let W:= ChamberU C L k; Priced (purseP W) (spinR targetPower) (fun i=> normalizationCoeff C L a i.top i.b) (fun i=> normalizationCoeff C L a i.summit i.b) E := by
    intro W; exact hear ((scripted C h L p hJ hk).vac _ hE) (chart_ok G) h a

-- direct application of approved rate to requested internal order anywhere on k-tail
open Pert.Asymptotics
lemma culled (c:ℝ)(hc: 1<c)(e r d:ℕ)(he:e ≤ E):
    let minN i:=i+ First.endV C.path.levels i ((Lambda C.path.levels i)^c)
    ∀ᶠ i in atTop, ∀ N≥ minN i, ∀ q,
    Bail (fame _) ((FamilyWindow C).width (C.path.levels.clock.J i)) (densityCoeff C L a N i e r - vacuumLimit C a L i e r) ((regulatorRun C N q i)^d) := by
   obtain ⟨A,m,H,W⟩:= Culminates C h a L p hJ hk hE he r
   intro N; filter_upwards [eventually_ge_atTop k, First.hearty p.available h c hc targetPower targetPower_pos d m (A*4^m) (mul_nonneg H (by positivity))] with i hi hu n hn q
   have hN:k≤ i:= hi; let z:=Lambda C.path.levels i; let V:= ageZ (C.path.levels.clock.hatBeta i)
   have hz:V ≤ 4*z := by have := (spend p.power i).2; have hk:1≤z:=First.lambda_large C.path.levels _; linarith
   refine ((W i hi).2.2 n (le_trans (show i≤N i from Nat.le_add_right ..) hn)).mono (le_trans ?_ (hu _ hn _))
   change A*V^m*ratioR _ n _ _ ≤ _; apply mul_le_mul_of_nonneg_right _ (ratioR_pos ..).le
   rw [mul_assoc,← mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (progZ (p.power.beta i))) hz m) H
end
end YM.FormalBulk08.Primer
