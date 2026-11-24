import YM.Integration.WilsonThermometerWeakIssuedDetector
import YM.MergeProof.West.Mooncake

/-! Hear the separately issued polynomials at their actual displaced Gaussian sites. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakDisplacedWick

open Function Filter RG RG12 Extra.Histories Lattice Wilson
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Source Labels
open Next.Rank.Configuration Normal Rise Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon
open Price Prayer Cells Common Marker Glyph Exponential Read Particle
open scoped Topology BigOperators Classical ContDiff

variable {G:Gauge} {C:Family G} {d k p n degree:ℕ} {d0:Fin n→ℕ}

theorem aligned {D:ℕ} (h:d≤D) {V:Type*} (f:V→Address G) (ρ:ℝ) (hp:0<ρ)
    (z:C.label d) (P:poly V)
    (filed:trim (exchange (ink d f) P) (key G d) d=expose (C.labels.level d) (Price.weightTag C d ρ z)) :
    trim (exchange (features D f ρ) P) bear d=rename Sum.inl (thawKey (raiseLabel G h ((C.labels.level d).coords.symm z))) := by
  rw [Perch.spaced D f ρ,jets_keep,costs_X h,filed,expose_at,alum_thaw h,thawKey]
  let w:=(C.labels.level d).coords.symm
  rw [show (raiseLabel G h (w (weightTag C d ρ z))).val=jets generation (ρ:ℂ) (raiseLabel G h (w z)).val from pure_weight (C:=C) ρ z,←peel,cycles]
  · rfl
  · exact Complex.ofReal_ne_zero.mpr hp.ne'

variable (hY:∀ i,d0 i≤d) (v:(i:Fin n)→C.label (d0 i))
def heat {b:ℕ} (wide:4*b≤wood C.path.levels k) (Y:AtlasData G C.S p) (W:poly (slotC G b)) :=
  milk (control (k:=k) Y 0 (wood C.path.levels k)) (rename (calls wide) W)

theorem offered (simple:G.Simple) (b:ℝ) (hb:0<b) (enough:∀ i,Atlas.saves C (d0 i)+3≤b) (degree:ℕ) :
    ∀ᶠ k:ℕ in atTop,∀ P:Fin n→poly (trimV (wood C.path.levels k) G),
    (∀ i,coin (P i) ≤ bill (b*d0 i + Atlas.saves C (d0 i)) (clim C.path.levels k)) →
    (∀ i,totalDegree (P i) ≤ degree) →
    (∀ i,trim (exchange (faceTest C (d0 i) k) (P i)) (key G (d0 i)) (d0 i)=expose (C.labels.level (d0 i)) (Price.weightTag C (d0 i) (Station.mag C.path.levels b k) (v i))) →
    let s:=clim C.path.levels k
    let ρ:=Station.mag C.path.levels b k
    ∃ X:Spend n degree, X.B=bill (fuel degree n) s ∧ X.collision=bill (-2) s ∧ X.cost=bill (-3/2) s ∧
      TollsX X d0 (fun _:Fin n=>features d (Subtype.val:trimV (lengthW s) G→Address G) ρ) P
        (fun i=>raiseLabel G (hY i) ((C.labels.level (d0 i)).coords.symm (v i))) ρ
        (fun i=>bill (b*d0 i + Atlas.saves C (d0 i)) s) (bill (fuel degree n) s) := by
  let A:=C.path.levels
  let f i:=thawKey (raiseLabel G (hY i) ((C.labels.level (d0 i)).coords.symm (v i)))
  let fee:ℝ:=(∑ i,coin (f i))+1
  have nn (i):0≤coin (f i):=Rise.sign _ _ zero_le_one
  have one:1≤fee:=by unfold fee; linarith only [Finset.sum_nonneg (s:=Finset.univ) fun i _=>nn i]
  filter_upwards [(hat_rate A simple).eventually (shed n degree fee one),
    (hat_rate A simple).eventually (radiant (G:=G) (d:=d) (n:=n) degree)] with k spend site
  intro P gross words filed
  let s:=clim A k
  let ρ:=Station.mag A b k
  have r1:1≤ρ:=by unfold ρ; rw [mag_bill]; exact Glimmer.costed _ _ hb.le
  obtain ⟨Q,hξ,hbase,hP,hB,hc⟩:=spend
  refine ⟨Q,hB,hP,hc,⟨r1,gross,words,?_,?_,Glimmer.costed _ _ (fuel_real degree n).le,?_,?_⟩⟩
  · intro i
    rw [hbase]
    exact (Finset.single_le_sum (f:=fun i=>coin (f i)) (fun i _=>nn i) (Finset.mem_univ i)).trans (le_add_of_nonneg_right zero_le_one)
  · intro _ z
    exact site _ _ ρ r1 z ((tracing _ _).mp z.property)
  · intro i
    exact aligned (hY i) _ ρ (zero_lt_one.trans_le r1) (v i) (P i) (filed i)
  intro i
  rw [hξ]
  change _ ≤ _ * (Station.mag A b k)^(d0 i+1)
  rw [mag_bill]
  exact Glimmer.ticket degree n (d0 i) (Atlas.saves C (d0 i)) b (enough i) s

variable {Y:AtlasData G C.S p} {x:Points n} {b:ℝ} (g:Fit C.path.levels b k x)

theorem sampled (P:Fin n→poly (trimV (wood C.path.levels k) G))
    (h:Atlas.Bell C.path.levels Y d degree g)
    (m:Chamber G C.S (middle C.path.levels b k) p→ℝ)
    (hm:Atlas.Wind C.path.levels m (fraction n degree (clim C.path.levels k)))
    (spend: let s:=clim C.path.levels k
            let ρ:=Station.mag C.path.levels b k
            ∃ X:Spend n degree, X.B=bill (fuel degree n) s ∧ X.collision=bill (-2) s ∧ X.cost=bill (-3/2) s ∧
              TollsX X d0 (fun _:Fin n=>features d (Subtype.val:trimV (lengthW s) G→Address G) ρ) P
                (fun i=>raiseLabel G (hY i) ((C.labels.level (d0 i)).coords.symm (v i))) ρ
                (fun i=>bill (b*d0 i+Atlas.saves C (d0 i)) s) (bill (fuel degree n) s))
    (hs:let s:=clim C.path.levels k
        Meridian d (Ship.fitting g) (G:=G) (fraction n degree s) (fraction n degree s)
          (bill (-3) s) (bill (fuel degree n) s) (bill (-2) s) (Station.mag C.path.levels b k) (lengthW s))
    (q:Glyph.modes (Fin n)) :
    let A:=C.path.levels
    let w:=Station.choose A b k x
    ‖(Answer Y w (before A b k) P (fun a=>(m a:ℂ))).part q-
      (Read.maxProfile C (Station.tested A b k x) (Atlas.jointX v)).part q‖ ≤ bill (-3/2) (clim A k) := by
  intro A w
  obtain ⟨U,hB,hc,hF,h₁⟩:=spend
  let M₀ := lengthW (clim A k)
  let l := Station.middle A b k
  let g₀ := (Subtype.val : trimV M₀ G → _)
  let Γ:= Γre A.S Y w (before A b k)
  let μ:= μre A.S Y w (before A b k) (fun x => (m x:ℂ))
  let K:= Γs A Y w (before A b k)
  let r:= mag A b k
  let Q := Qmarks Y w (before A b k); let U' := noise Y w (before A b k) (fun x => (m x:ℂ))
  let f := fun i : Fin n × trimV M₀ G => (i.1,i.2.val)
  let S := primary d g₀ r Γ K
  let V := Beamer.seen d g₀ r μ
  let L := Normal.perSlot (fun _ : Fin n => features d g₀ r)
  have hT : Normal.scope (fun i => Finsupp.single (f i) 1) Q=Normal.scope L S := by
    have ht : Normal.scope L S=prize g₀ Γ K := shaped d g₀ r Γ K (zero_lt_one.trans_le h₁.radius)
    rw [ht]; apply Normal.Symmetric.ext; funext i j; rw [Normal.match_name f]; exact (h.validQ ..).symm
  have hv : U' ∘ f= Normal.reads L V := by
    funext i; rw [show Normal.reads L V i= _ from scanned d g₀ r μ i (zero_lt_one.trans_le h₁.radius)]
    exact (h.validM m hm _).symm
  have hh := Prayer.resolution d (Ship.fitting g) r _ hs g₀ (fun i => (tracing ..).1 i.property) Γ μ K (h.verdict m hm)
  rw [Answer_part, stagesX _ hY _ (Ship.fitting g),← hF]
  exact Particle.acuity h₁ (Ship.fitting g) S V q _ _ hT hv (hB ▸ hh.1) (hB ▸ hc ▸ hh.2)

end YM.Integration.WilsonAddressedWeakDisplacedWick


