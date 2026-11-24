import YM.Integration.WilsonReportDisjointBack

/-! The exact signed finite sector invoice against an independently scheduled fine exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportFlagSectors
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker
open Push Push.GridApprox OPE OPE.Strobe OPE.Yarn OPE.Strobe.Vista26
open Extra.Multi Next.Rank Next.Rank.Spindle PhysicalNext.Repeat.Legato MergeProof.Ribbons.ManyCopies.Patrol
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V] {W r D} {k N p : ℕ}

private theorem expansion (s : Finset V) (a b c w z : V→ℂ)
    (active : ∀ j, z j=a j-b j) (quiet : ∀ j, w j=a j-c j) :
    (∏ j∈s,a j)-(∏ j∈s,b j) =
    ∑ T∈s.powerset.erase ∅, ∑ U∈(s\T).powerset,
      (-((-1:ℂ)^T.card)*(∏ j∈(s\T)\U,c j))*((∏ j∈T,z j)*(∏ j∈U,w j)) := by
  let h (T : Finset V) := ((-1:ℂ)^T.card)*(∏ j∈s\T,a j)*(∏ j∈T,z j)
  have right : (∏ j∈s,b j) = ∑ T∈s.powerset,h T := by
    change _ = ∑ T∈s.powerset,((-1:ℂ)^T.card)*(∏ j∈s\T,a j)*(∏ j∈T,z j)
    rw [←prod_sub]
    exact prod_congr rfl fun j _ => by rw [active]; ring
  have empty : h ∅=∏ j∈s,a j := by simp [h]
  have step : (∏ j∈s,a j)-(∏ j∈s,b j) = ∑ T∈s.powerset.erase ∅, -h T := by
    rw [right,←sum_erase_add _ h (by simp : (∅ : Finset V)∈s.powerset),empty,Finset.sum_neg_distrib]
    ring
  rw [step]
  refine sum_congr rfl fun T _ => ?_
  have left : (∏ j∈s\T,a j) = ∑ U∈(s\T).powerset,(∏ j∈U,w j)*(∏ j∈(s\T)\U,c j) := by
    rw [←prod_add]
    exact prod_congr rfl fun j _ => by rw [quiet]; ring
  dsimp only [h]
  rw [left,Finset.mul_sum,Finset.sum_mul,←Finset.sum_neg_distrib]
  exact sum_congr rfl fun U _ => by ring

def column (d : V→ℕ) (v : (j:V)→C.label (d j)) (s T U : Finset V) : ℂ :=
  -((-1:ℂ)^T.card)*∏ j∈(s\T)\U, cameo C (d j) k N p (v j)

/-- T is the genuinely changed nonempty sector; the surviving partners U keep
the false Strobe flag, all under the original fine field and actual regulator. -/
def flags (hk : k≤N) (d : V→ℕ) (x : V→Site (C.side k p)) (v : (j:V)→C.label (d j))
    (T U : Finset V) (Z : Config G (C.side N p)) : ℂ :=
  (∏ j∈T, writeF C (v j) N k p (C.path.levels.budget k).B (x j) hk true Z) *
    ∏ j∈U,writeF C (v j) N k p (C.path.levels.budget k).B (x j) hk false Z

private theorem point (hk : k≤N) (d : V→ℕ) (x : V→Site (C.side k p)) (v : (j:V)→C.label (d j))
    (s : Finset V) (Z : Config G (C.side N p)) :
    fineJob (BarePack d x hk v) s Z-fineJob (fun j => backTo C.path N p hk (ScenePack (N:=N) d x v j)) s Z =
      ∑ T∈s.powerset.erase ∅,∑ U∈(s\T).powerset,column (k:=k) (N:=N) (p:=p) d v s T U*flags hk d x v T U Z := by
  apply expansion
  · intro j
    exact congr_fun (erased (k:=k) (v j) (C.path.levels.budget k).B (x j) hk true) Z
  · intro j
    exact congr_fun (erased (k:=k) (v j) (C.path.levels.budget k).B (x j) hk false) Z

private theorem times {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X F : Ω→ℂ}
    (iX : Integrable X μ) (eF : Envelope F) : Integrable (fun Z => X Z*F Z) μ := by
  obtain ⟨a,cap⟩ := eF.cost
  exact iX.mul_bdd eF.meas.aestronglyMeasurable (Eventually.of_forall cap)

/-- Full marked finite sum, retaining the complex signs of the independently
specified fine spectator before taking any norm. -/
def signed (hk : k≤N) (d : V→ℕ) (x : V→Site (C.side k p)) (v : (j:V)→C.label (d j))
    (s : Finset V) (X : Config G (C.side N p)→ℂ) : ℂ :=
  ∑ T∈s.powerset.erase ∅,∑ U∈(s\T).powerset,column (k:=k) (N:=N) (p:=p) d v s T U *
    moment (C.beta N p) (fun Z => X Z*flags hk d x v T U Z)

def invoice (hk : k≤N) (d : V→ℕ) (x : V→Site (C.side k p)) (v : (j:V)→C.label (d j))
    (s : Finset V) (X : Config G (C.side N p)→ℂ) : ℝ :=
  ∑ T∈s.powerset.erase ∅,∑ U∈(s\T).powerset,‖column (k:=k) (N:=N) (p:=p) d v s T U‖ *
    ‖moment (C.beta N p) (fun Z => X Z*flags hk d x v T U Z)‖

theorem charge (hk : k≤N) (d : V→ℕ) (x : V→Site (C.side k p)) (v : (j:V)→C.label (d j))
    (s : Finset V) (X : Config G (C.side N p)→ℂ) :
    ‖signed hk d x v s X‖ ≤ invoice hk d x v s X := by
  unfold signed invoice
  refine (norm_sum_le _ _).trans (sum_le_sum fun T _ => ?_)
  exact (norm_sum_le _ _).trans (sum_le_sum fun U _ => (norm_mul _ _).le)

/-- On the admitted true separated sites, the sole fine error is exactly these
nonempty signed microscopic sectors with all their actual quiet partners.
The independent fine spectator may be any integrable measurable observable. -/
theorem original [Fintype V] (hG : G.Simple) (hC : C.Makes) (citizen : Citizen C W r D)
    (d : V→ℕ) : ∀ᶠ k : ℕ in atTop, ∀ N p, ∀ hk : k≤N, ∀ x : V→Site (C.side k p),
    (∀ a b,a≠b → (C.path.levels.budget k).B^8 ≤ Lattice.separation (x a) (x b)) →
    ∀ v : (j:V)→C.label (d j), ∀ s : Finset V, ∀ X : Config G (C.side N p)→ℂ,
    Integrable X (law G (C.side N p) (C.beta N p)) →
    moment (C.beta N p) (fun Z => X Z*fineJob (BarePack d x hk v) s Z) -
      moment (C.beta N p) (fun Z => X Z*backTo C.path N p hk (fineJob (ScenePack (N:=N) d x v) s) Z)
      = signed hk d x v s X := by
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  filter_upwards [WilsonReportDisjointBack.entire hG hC citizen d,
    eventually_all.mpr (fun j : V => eventually_ge_atTop (C.ref (d j)))] with k back refs N p hk x apart v s X iX
  rw [back N p hk x apart v s]
  let μ := law G (C.side N p) (C.beta N p)
  let A := fineJob (BarePack d x hk v) s
  let B := fineJob (fun j => backTo C.path N p hk (ScenePack (N:=N) d x v j)) s
  let c := column (k:=k) (N:=N) (p:=p) d v s
  let e := flags hk d x v
  have eA : Envelope A := Envelope.prodC s _ (fun _ _ => Envelope.compactC (C.continuousO ..))
  have eB : Envelope B := Envelope.prodC s _ fun j _ => backTo_env C.path N p hk
    (cylinder_env (Strobe.bead_local H _ (v j) (refs j) hk _))
  have terms (T U : Finset V) : Envelope (e T U) := (Envelope.prodC T _ (fun j _ =>
    Strobe.write_e H (v j) _ (x j) hk (refs j) true)).mulC
      (Envelope.prodC U _ (fun j _ => Strobe.write_e H (v j) _ (x j) hk (refs j) false))
  let f := fun T U Z => c T U*(X Z*e T U Z)
  have iF (T U : Finset V) : Integrable (f T U) μ := (times iX (terms T U)).const_mul _
  change (∫ Z, X Z*A Z ∂μ)-(∫ Z,X Z*B Z ∂μ) =
    ∑ T∈s.powerset.erase ∅,∑ U∈(s\T).powerset,c T U*(∫ Z,X Z*e T U Z ∂μ)
  rw [←integral_sub (times iX eA) (times iX eB)]
  have eq (Z) : X Z*A Z-X Z*B Z=∑ T∈s.powerset.erase ∅,∑ U∈(s\T).powerset,f T U Z := by
    rw [←mul_sub,point hk d x v s Z,Finset.mul_sum]
    apply sum_congr rfl
    intro T _
    rw [Finset.mul_sum]
    exact sum_congr rfl fun U _ => by dsimp only [f,c,e]; ring
  simp_rw [eq]
  rw [integral_finsetSum _ (fun T _ => integrable_finsetSum _ fun U _ => iF T U)]
  refine sum_congr rfl fun T _ => ?_
  rw [integral_finsetSum _ (fun U _ => iF T U)]
  exact sum_congr rfl fun U _ => integral_const_mul _ _

end YM.Integration.WilsonReportFlagSectors
end

