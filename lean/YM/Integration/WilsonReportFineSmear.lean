import YM.Integration.WilsonReportFlagSectors
import YM.Integration.WilsonReportFineCumulant
import YM.OPE.Samples.Layout

/-! Original finite Order.smears with the signed interior and its independently
placed microscopic exterior. The genuine tested offset and early flags survive. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportFineSmear
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol Push.GridApprox
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {W r D} {n a k N p : ℕ}

abbrev Sites (C : Family G) (N p n a : ℕ) := Fin (n+a)→Site (C.side N p)

def parents (hk : k≤N) (y : Sites C N p n a) (j : Fin n) : Site (C.side k p) :=
  (C.S.toDepth hk p).parent (y (Fin.castAdd a j))

def weight (C : Family G) {N p l : ℕ} (ψ : Test l) (y : Fin l→Site (C.side N p)) : ℂ :=
  (C.S.a N:ℂ)^(4*l)*ψ (Order.cells C N p y)

def exterior (tokens : Fin a→C.book.Token) (y : Sites C N p n a) (Z : Config G (C.side N p)) : ℂ :=
  ∏ j,C.seen (tokens j) (y (Fin.natAdd n j)) Z

def rooted (d : Fin n→ℕ) (v : (j:Fin n)→C.label (d j)) (y : Sites C N p n a)
    (Z : Config G (C.side N p)) : ℂ := ∏ j,C.O N p (v j) (y (Fin.castAdd a j)) Z

/-- The literal microscopic regulator insertion minus the insertion at the
actual ancestor's root; the external fields stay inside this signed moment. -/
def offset (hk : k≤N) (d : Fin n→ℕ) (v : (j:Fin n)→C.label (d j))
    (E : Fin a→C.book.Token) (y : Sites C N p n a) : ℂ := moment (C.beta N p) fun Z =>
  exterior E y Z*(rooted d v y Z-fineJob (BarePack d (parents hk y) hk v) univ Z)

def early (hk : k≤N) (d : Fin n→ℕ) (v : (j:Fin n)→C.label (d j))
    (E : Fin a→C.book.Token) (y : Sites C N p n a) : ℂ :=
  WilsonReportFlagSectors.signed hk d (parents hk y) v univ (exterior E y)

def sampled (hk : k≤N) (d : Fin n→ℕ) (v : (j:Fin n)→C.label (d j))
    (E : Fin a→C.book.Token) (y : Sites C N p n a) : ℂ := moment (C.beta N p) fun Z =>
  exterior E y Z*backTo C.path N p hk (fineJob (regularPack (N:=N) d (parents hk y) v) univ) Z

private theorem numeric (d : Fin n→ℕ) (v : (j:Fin n)→C.label (d j)) (E : Fin a→C.book.Token)
    (y : Sites C N p n a) :
    C.numeric N p (Fin.append (fun j => ⟨d j,v j⟩) E) y =
      moment (C.beta N p) (fun Z => exterior E y Z*rooted d v y Z) := by
  change moment (C.beta N p) (fun Z => ∏ j,C.seen ((Fin.append (fun j => ⟨d j,v j⟩) E) j) (y j) Z) = _
  apply congrArg
  funext Z
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  exact mul_comm .. 

private theorem signed_offset (hk : k≤N) (d : Fin n→ℕ) (v : (j:Fin n)→C.label (d j))
    (E : Fin a→C.book.Token) (y : Sites C N p n a) :
    moment (C.beta N p) (fun Z => exterior E y Z*rooted d v y Z)-
      moment (C.beta N p) (fun Z => exterior E y Z*fineJob (BarePack d (parents hk y) hk v) univ Z) =
      offset hk d v E y := by
  have outside : Continuous (exterior E y) := continuous_finsetProd _ fun j _ => C.continuousO N p _ _ _
  have microscopic : Continuous (rooted d v y) := continuous_finsetProd _ fun j _ => C.continuousO N p _ _ _
  have anchors : Continuous (fineJob (BarePack d (parents hk y) hk v) univ) :=
    continuous_finsetProd _ fun j _ => C.continuousO N p _ _ _
  change (∫ Z,exterior E y Z*rooted d v y Z ∂law G _ _)-(∫ Z,exterior E y Z*_ ∂_) = _
  have i₁ : Integrable (fun Z => exterior E y Z*rooted d v y Z) (law G (C.side N p) (C.beta N p)) :=
    continuous_integrable (C.beta N p) (outside.mul microscopic)
  have i₂ : Integrable (fun Z => exterior E y Z*fineJob (BarePack d (parents hk y) hk v) univ Z)
      (law G (C.side N p) (C.beta N p)) := continuous_integrable (C.beta N p) (outside.mul anchors)
  rw [←integral_sub i₁ i₂]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => (mul_sub ..).symm)

/-- Two physical positions separated on the actual wrapped Wilson torus
retain the required stage spacing after passing to their original parents. -/
theorem parent_spacing (hk : k≤N) (u v : Site (C.side N p)) (b : ℕ)
    (space : 2*C.S.a k*b≤‖C.S.place (u-v)‖) :
    b ≤ separation ((C.S.toDepth hk p).parent u) ((C.S.toDepth hk p).parent v) := by
  let F := C.S.toDepth hk p
  have mesh : C.S.a N*(F.count.val:ℝ)=C.S.a k := C.S.embeds_scale F
  have ambient := (MergeProof.Ribbons.normC C N p (u-v)).2
  have shift : separation (u-v) 0=separation u v := by simp [separation]
  rw [shift] at ambient
  have scale0 : 0<2*C.S.a N := mul_pos (by norm_num) (C.S.a_pos N)
  have scaled : (F.count.val*b:ℕ) ≤ separation u v := by
    suffices h : ((F.count.val*b:ℕ):ℝ)≤(separation u v:ℝ) by exact_mod_cast h
    apply le_of_mul_le_mul_left _ scale0
    calc
      _ = 2*C.S.a k*b := by rw [Nat.cast_mul,←mesh]; ring
      _ ≤ _ := space.trans ambient
  have exact_dist := (OPE.Log.Trunk.Canvas.expands (C:=C) u v hk).2
  change separation u v < F.count.val*separation (F.parent u) (F.parent v)+F.count.val at exact_dist
  change b ≤ separation (F.parent u) (F.parent v)
  by_contra! low
  have no_room := Nat.mul_le_mul_left F.count.val (Nat.succ_le_of_lt low)
  rw [Nat.mul_succ] at no_room
  exact (not_le_of_gt exact_dist) (no_room.trans scaled)

/-- With the exact torus mesh, original signed test, microscopic external labels
and full summed coarse field, only the displayed original offset and nonempty
charged sectors remain. Their joint signed sum is conserved. This exponential
radius estimate uses no diameter bound for the independent exterior. -/
theorem purchased (hG : G.Simple) (hC : C.Makes) (book : Log.OnBudget C.path.levels)
    (citizen : Citizen C W r D) (d : Fin n→ℕ) (t : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ N p, ∀ hk : k<N, ∀ v : (j:Fin n)→C.label (d j),
    (∀ j,Spindle.paid C (d j) k N p (v j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ a : ℕ, ∀ E : Fin a→C.book.Token, ∀ ψ : Test (n+a),
    (∀ y : Sites C N p n a,ψ (Order.cells C N p y)≠0 →
       ∀ j l : Fin n,j≠l → 2*C.S.a k*((C.path.levels.budget k).B^8:ℕ) ≤
          ‖C.S.place (y (Fin.castAdd a j)-y (Fin.castAdd a l))‖) →
    ‖Order.smears C N p (Fin.append (fun j => ⟨d j,v j⟩) E) ψ-
      ∑ y : Sites C N p n a,weight C ψ y*(sampled hk.le d v E y+offset hk.le d v E y+early hk.le d v E y)‖ ≤
    ∑ y : Sites C N p n a, ‖weight C ψ y‖*((∫ Z,‖exterior E y Z‖ ∂law G (C.side N p) (C.beta N p))*
      Real.exp (-((C.path.levels.budget k).B:ℝ))) := by
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  filter_upwards [WilsonReportFlagSectors.original hG hC citizen d,
    WilsonReportExteriorBudget.purchased hG hC book citizen d t,
    eventually_all.mpr (fun j : Fin n => eventually_ge_atTop (C.ref (d j)))] with k flags radius refs
  intro N p hk v funds a E ψ geometry
  let μ := law G (C.side N p) (C.beta N p)
  let tokens := Fin.append (fun j => (⟨d j,v j⟩:C.book.Token)) E
  let b := Real.exp (-((C.path.levels.budget k).B:ℝ))
  have per (y : Sites C N p n a) (support : ψ (Order.cells C N p y)≠0) :
      ‖C.numeric N p tokens y-(sampled hk.le d v E y+offset hk.le d v E y+early hk.le d v E y)‖≤
        (∫ Z,‖exterior E y Z‖ ∂μ)*b := by
    let x := parents hk.le y
    let X := exterior E y
    let P := fineJob (regularPack (N:=N) d x v) univ
    let Q := fineJob (ScenePack (N:=N) d x v) univ
    let cap := fineJob (BarePack d x hk.le v) univ
    have iX : Integrable X μ := C.integrableR E (fun j => y (Fin.natAdd n j))
    have fine : Integrable X (Therm.scene C.path N p N) := by rw [WilsonReportForwardTransfer.top hC]; exact iX
    have apart (j l : Fin n) (ne : j≠l) : (C.path.levels.budget k).B^8 ≤ separation (x j) (x l) :=
      parent_spacing hk.le _ _ _ (geometry y support j l ne)
    have Δ := flags N p hk.le x apart v univ X iX
    have off := signed_offset hk.le d v E y
    have ep : Envelope P := Envelope.prodC univ _ (fun j _ => wholeEnv H citizen (v j) (x j) hk (refs j))
    have eq : Envelope Q := Envelope.prodC univ _ (fun j _ => cylinder_env (Strobe.bead_local H _ (v j) (refs j) hk.le _))
    let Y := WilsonReportForwardTransfer.exterior (N:=N) hk.le X
    have mass := WilsonReportForwardTransfer.contract hC hk.le le_rfl X fine
    have pQ := WilsonReportForwardTransfer.joint hC hk.le le_rfl X fine Q eq
    have pP := WilsonReportForwardTransfer.joint hC hk.le le_rfl X fine P ep
    have pay := radius N p hk x v funds univ Y mass.1
    have cash := mass.2
    rw [WilsonReportForwardTransfer.top hC N p] at pQ pP cash
    change ‖(∫ U,Y U*P U ∂_)-(∫ U,Y U*Q U ∂_)‖≤_*b at pay
    rw [pP,pQ] at pay
    let fineQ := moment (C.beta N p) (fun Z => X Z*backTo C.path N p hk.le Q Z)
    change ‖sampled hk.le d v E y-fineQ‖≤_ at pay
    change moment (C.beta N p) (fun Z => X Z*cap Z)-fineQ=early hk.le d v E y at Δ
    have inv : C.numeric N p tokens y=offset hk.le d v E y+early hk.le d v E y+fineQ := by
      rw [numeric d v E y]
      change moment (C.beta N p) (fun Z => X Z*rooted d v y Z)-moment (C.beta N p) (fun Z => X Z*cap Z)=_ at off
      linear_combination off+Δ
    rw [inv]
    calc
      _ = ‖fineQ-sampled hk.le d v E y‖ := congrArg norm (by ring)
      _ = ‖sampled hk.le d v E y-fineQ‖ := norm_sub_rev ..
      _ ≤ _ := pay.trans (mul_le_mul_of_nonneg_right cash (Real.exp_nonneg _))
  have raw : Order.smears C N p tokens ψ=∑ y : Sites C N p n a, weight C ψ y*C.numeric N p tokens y := by
    rw [Order.smears,Finset.mul_sum]
    exact sum_congr rfl fun _ _ => (mul_assoc ..).symm
  rw [raw,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro y _
  rw [←mul_sub,norm_mul]
  by_cases zero : ψ (Order.cells C N p y)=0
  · simp only [weight,zero,mul_zero,norm_zero,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (per y zero) (norm_nonneg _)

end YM.Integration.WilsonReportFineSmear
end

