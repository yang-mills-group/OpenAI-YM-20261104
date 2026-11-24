import YM.Integration.WilsonMovingForkProbeMaster

/-! One original election and one physical stop for every complete and every
reflected Gram reading on the named public basis. The finite optical
matrices are fixed before all screened locations of a given trial. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkProbeEars
open Function Filter Finset Set Metric Lattice Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedGridTree WilsonSeparatedBranchStencil
open OPE RG16 RG16.Literal RG17 FVA2 FVA2.Register MS MS.Land PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonReflectedPublicStationFare (station)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonMovingForkHeterogeneousCut (Filed Heard Invoice)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
  (J:ℝ → tower S)(Z:WilsonPrescription G){I:Type}[Fintype I][DecidableEq I][Nonempty I]

omit [DecidableEq I] [Nonempty I] in
def Charge (D T B:ℕ)(d:I → Fin (D+1))(x:∀i,Free R.family (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(η M:ℝ)
    (u P q n:ℕ)(lookup:Fin n ↪ I)(E:Type)[Fintype E]:Prop:=
    ∃m:ℕ,∃C₀ D₀:ℝ,0 ≤ C₀ ∧ 0 < D₀ ∧ ∀ᶠr in trail,∀rp:0 < r,∀ρ:I → {s:ℝ // 0 < s ∧ s < δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z B r) → (∃i,(ρ i).val=r) →
      let j:=reporter F books ρ
      let dp:=div_pos (R.family.S.a_pos j) rp
      let select:=fun i:Fin n=>lookup i
      let di:=fun i=>(d (select i)).val
      ∃_uj:u ≤ j,∀weak:Fin n → Bool,
      let v:=fun i=>homogeneous F J Z (ρ (select i)).val (di i) (x (select i))
      let book:=fun i=>(books (ρ (select i))).rows (d (select i))
      let arms:=fun i=>(book i).arm (weak i) (v i)
      ∀K:ℕ,∀jK:j ≤ K,∀b:Filed R di K,(∀i,b.station i=station F (book i) (weak i)) →
      ∀t c:ℕ,∀ut:u ≤ t,∀tc:t ≤ c,∀ck:c ≤ K,
      ∀pred:Points n → ℂ,∀w:Invoice,0 ≤ w.total t c K →
      let good:=fun o:Fin n → Cover=>(∀i,‖R.family.S.gridPoint j (o i)‖ ≤ (M+1)*outer z B r) ∧
        (Pairwise fun i k=>(η/2)*r ≤ ‖R.family.S.gridPoint j (o i)-R.family.S.gridPoint j (o k)‖)
      (∀o,good o → Heard (f:=f) b ut tc ck jK arms o pred w) →
      ∀ref:E → E4,∀X:Points n,(∀i,‖r • X i‖ ≤ M*outer z B r) → (∀i k,i≠k → η ≤ dist (X i) (X k)) →
      let prog:=sold m ref dp X
      let values:=fun y:Points n=>pred (r • y)
      (∀N per, K < N → ∀i,
        b.A N per i (WilsonMovingForkMixedSeed.doses R di b.station (N:=N) (per:=per) (b.A N per)
          (fun h=>(arms h).source (N,per)) i)=WilsonOriginalMicroscopicGuardedPage.full R (di i) N per
          (station F (book i) (weak i)) ((arms i).source (N,per))) ∧
      ‖S.classMoment S di (r • X) v-pred (r • X)‖ ≤ C₀*(∏i:Fin n,‖x (select i)‖)*(wilson z r)^P+
        (total n m E)^levels n*(D₀*(wilson z r)^q+w.total t c K)+‖read prog values-values X‖

variable {n h:ℕ}{P:Type}[Fintype P][DecidableEq P]
open WilsonMovingForkProbeMaster

theorem original (order:(l:Filter _) ≤ f.fuse)(fac:Facilities R.family f S)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (T B:ℕ)(d:Fin n → ℕ)(v:∀i,Free R.family (d i))(a:P→Free R.family h)
    {δ η M:ℝ}(dp:0<δ)(ep:0<η)(mp:0≤M)
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z (cap h d) T s.val)
    (priced:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃J₀ u:ℕ,Stop R.family 0 J₀ u ∧ ∀pay q:ℕ,∀E:Type,∀[Fintype E],
      let ds:=bound (G:=G) (h:=h) (P:=P) d
      let xs:=dose d v a
      (∀j,Charge F J Z (cap h d) T B ds xs books η M u pay q (n+1) (whole j) E) ∧
      (∀k j,Charge F J Z (cap h d) T B ds xs books η M u pay q 2 (pair k j) E):=by
  obtain ⟨J₀,u,stop,all⟩:=WilsonMovingForkCommonEar.original F J Z order fac bliss slow lead owed
    (cap h d) T B (bound (G:=G) (h:=h) (P:=P) d) (dose d v a) dp ep mp books priced
  refine ⟨J₀,u,stop,?_⟩
  intro pay q E inst ds xs
  have at_face {m:ℕ}(has:0 < m)(look:Fin m ↪ Seat G n h P):Charge F J Z (cap h d) T B ds xs books η M u pay q m look E:=by
    let index:=visit look
    have active:(subface look).Nonempty:=⟨_,(index ⟨0,has⟩).property⟩
    exact all pay q (subface look) active m index E
  exact ⟨fun j=>at_face (Nat.succ_pos _) (whole j),fun k j=>at_face (by decide) (pair k j)⟩

end YM.Integration.WilsonMovingForkProbeEars
