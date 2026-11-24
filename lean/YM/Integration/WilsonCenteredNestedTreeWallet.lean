import YM.Integration.WilsonCenteredNestedThreeArms
import YM.Integration.WilsonCenteredNestedSharedField

/-! A fixed finite set of independently paid original raw tickets
suffices before every angle, placement and every input amplitude.
The signed difference of the two complete raw fields is expanded first. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreeWallet
open Function Filter Set Finset Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Log OPE.Nesting OPE.Nesting.Tree WilsonCenteredNestedLoggedRow WilsonCenteredNestedShadowBasis
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedPairConvoy WilsonCenteredNestedTicketSites
open WilsonCenteredNestedRawDiagram WilsonCenteredNestedThreeArms
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def toll (d:Fin 3→ℕ) (m:ℕ) (a r:ℝ) := a^(d 0+d 1)*r^(d 2)/r^m

lemma basis (fac : Facilities C f S) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (d:Fin 3→ℕ) (v:Labels S d)
    (w:Mode F.sector.derivatives) (D:ℕ) {M η:ℝ} (Mn:0≤M) (ηp:0<η) :
    ∃ j:ℕ,∀ᶠ r:ℝ in 𝓝[>]0,∀ (a:ℝ) (z:full.Plot),Accept r M η (dates r a) z →
      ∀ k:Ortho,toll d w.1 a r * ‖row F Q d D w (Ortho.move k ∘sites z) v‖ ≤
        (shell r * shell a)^j * (a/r)^(D+1) := by
  obtain ⟨l,priced⟩:=WilsonCenteredNestedPairTicket.original F Q fac lo ticket (named (tags v)) w D Mn ηp
  refine ⟨l,?_⟩
  have below : ∀ᶠr:ℝ in 𝓝[>]0,r<1 := (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [priced,below] with r atR small a z ok k
  have rp : 0<r := ok.levels.1
  have ap : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  have ar : a≤r := by
    have e : a≤r*1 := (ok.levels.2.2 (0:Fin 2)).2.1
    rwa [mul_one] at e
  have shellR : 1+OPE.run r=shell r := by unfold OPE.run shell;rw [abs_of_nonpos (Real.log_nonpos rp.le small.le)]
  have shellA : 1+OPE.run a=shell a := by unfold OPE.run shell;rw [abs_of_nonpos (Real.log_nonpos ap.le (ar.trans small.le))]
  have unit:=atR a z ok k
  rw [WilsonCenteredNestedThreeArms.original]
  rw [shellR,shellA] at unit
  exact unit

private lemma sum_price {ι:Type} [Fintype ι] (p h:ι→ℂ) (T B:ℝ) (nonneg:0≤T)
    (paid:∀i,T*‖h i‖≤B) : T*‖∑i,p i • h i‖ ≤ (∑i,‖p i‖)*B := by
  apply (mul_le_mul_of_nonneg_left (norm_sum_le Finset.univ (fun i=>p i • h i)) nonneg).trans
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,mul_left_comm T]
  exact mul_le_mul_of_nonneg_left (paid i) (norm_nonneg _)

private lemma basis_sum {I:Type} [Fintype I] {d:I→ℕ} (A: MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ)
    (v:Labels S d) (T B:ℝ) (nonneg:0≤T) (paid:∀t:Slot S d,T*‖A (axis S d t)‖≤B) :
    T*‖A v‖ ≤ mass v * B := by
  rw [expand A v]
  exact sum_price (coeff v) (fun t=>A (axis S d t)) T B nonneg paid

theorem original (fac : Facilities C f S) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (d:Fin 3→ℕ)
    (w:Mode F.sector.derivatives) (D:ℕ) {M η:ℝ} (Mn:0≤M) (ηp:0<η) :
    ∃ j:ℕ,∀ᶠ r:ℝ in 𝓝[>]0,∀ (a:ℝ) (z:full.Plot),Accept r M η (dates r a) z →
      ∀(k:Ortho)(v:Labels S d),toll d w.1 a r * ‖row F Q d D w (Ortho.move k ∘sites z) v‖ ≤
        mass v * ((shell r * shell a)^j * (a/r)^(D+1)) := by
  have src (t:Slot S d) := basis F Q fac lo ticket d (axis S d t) w D Mn ηp
  choose l priced using src
  let j := ∑t,l t
  refine ⟨j,?_⟩
  filter_upwards [eventually_all.mpr priced] with r atR a z ok k v
  have rp : 0<r := ok.levels.1
  have ap : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  have one : 1 ≤ shell r * shell a := one_le_mul_of_one_le_of_one_le (shell_one r) (shell_one a)
  have cost : 0≤toll d w.1 a r := by unfold toll;positivity
  apply basis_sum _ v _ _ cost
  intro t
  have hi : l t≤j := Finset.single_le_sum (f:=l) (fun _ _=>Nat.zero_le _) (Finset.mem_univ t)
  exact (atR t a z ok k).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one hi) (pow_nonneg (div_nonneg ap.le rp.le) _))

end YM.Integration.WilsonCenteredNestedTreeWallet
