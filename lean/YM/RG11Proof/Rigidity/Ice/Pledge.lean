import YM.RG11Proof.Rigidity.Ice.Lab

/-!
# Absence of charge: B probes have the same clocks under the finite
engineering pose. Here they can also certify the Gram condition before the
spherical analyzer needs it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Horizon Labels Pert.Position Pert Maxwell Function Extra.FD Reads Maxwell.Free Crowd Prism
open scoped Classical BigOperators InnerProductSpace
variable {G:Gauge}(F:Frames G){d:ℕ}

def place (n:ℕ)(p : WickPol G)(h:p∈shellSector G n): E F n := (exactField F n).symm ⟨p,h⟩
lemma place_reads (n p)(h:p∈shellSector G n): writes F n (place F n p h)=p := by
  change ((exactField F n) (_:E F n)).val= _; unfold place; rw [(exactField F n).apply_symm_apply]

def banner₀ (p q:Foil):E F 4:= place F _ (team G (cell p.1 p.2) (cell q.1 q.2)) (team_label _ _ le_rfl)
def banner (he:4≤d)(p q:Foil):= up F he (banner₀ F p q)
lemma banner_reads (h:4≤d)(p q):writes F d (banner F h p q)= canon (bloc G ((p,0),q,0)):= by rw [banner,up_write,banner₀,place_reads,bloc_team]

structure News (F : Frames G)(d : ℕ) where
  n : ℕ
  price : n ≤ d
  v : E F d
  real : Basis.overReals v
  base : v∈ lower F n d
  gr : grain n (writes F d v)

variable {F}
def sources : Performer G (News F d):=
   { deadline t:=t.n
     slate t:=course t.v t.base t.real
     refund t:=(drawn t.v t.base t.real).2 }

def posed (b : Buffer F d)(z:ℝ): Performer G (News F d):=
   { deadline t:=t.n
     slate t:=course (drive b.val t.v z) (directs b z _ t.price t.base) (drive_real b z _ t.real)
     refund _:=(drawn _ _ _).2 }

lemma Frigid.pledge {b:Buffer F d}(h:Frigid b)(he:4 ≤ d)(hG : G.Simple)(t:ℝ): Desert sources (posed b t):= by
  refine freezeDesert rfl (fun n x hx f=> ?_)
  let p : Fin n→ E F d := fun i=> Sum.elim (fun v:Panel=>banner F he v.1.1 v.2.1) (fun v=>News.v v) (f i)
  have ha (i) : canon (Sum.elim (bloc G) (sources (F:=F) (d:=d)).slate (f i))=writes F d (p i):= by
    dsimp only [p]
    cases f i with
    | inl k=> exact (bloc_team k).trans ((banner_reads F he k.1.1 k.2.1).trans (bloc_team _)).symm
    | inr k=> exact (drawn k.v k.base k.real).1
  have hb (i) : canon (Sum.elim (bloc G) (posed b t).slate (f i))=writes F d (drive b.val (p i) t):=by
    dsimp only [p]; cases f i with
    | inl k =>
      change canon (bloc G k)=writes F d (drive b.val (banner F he k.1.1 k.2.1) t)
      rw [drive_anchor _ (banner F he k.1.1 k.2.1) (h.four he hG _)]; exact (bloc_team k).trans ((banner_reads F he k.1.1 k.2.1).trans (bloc_team _)).symm
    | inr k => exact (drawn (drive b.val k.v t) (directs b t _ k.price k.base) (drive_real b t _ k.real)).1
  simp_rw [ha,hb,← writes_pair,h.stay _ _ hx]

lemma banner_graded (he : 4≤d)(p q:Foil): grain 4 (writes F d (banner F he p q)):=by
  rw [banner_reads,bloc_team]; unfold team; apply MvPolynomial.IsWeightedHomogeneous.sum; intro i _
  exact (symbol_hom (flavor 0 i (cell p.1 p.2)) (fun i=>i+2)).mul (symbol_hom (flavor 0 i (cell q.1 q.2)) (fun i=>i+2))

def scoop (he : 4 ≤ d): News F d where
  n:=4
  price:=he
  v:=banner F he (0,1) (0,1)
  real:=by
    apply writes_inj F d
    rw [writes_bar, banner_reads]; exact canon_real _
  base:= (staircase F he) ▸ (show _∈LinearMap.range (up F he) from ⟨_,rfl⟩)
  gr:=banner_graded he _ _

lemma paint_cell (v:G.Color)(M:Mirror G): available (paint (fun c j=> if h : 0=j then v c • (h ▸ blade (0:Axis) 1 (1:ℝ)) else 0) M 0) (cell 0 1)=grid M v:=by
  ext1 i
  change cell _ _ (faceMap _ (cp i) _)= ∑ j, M (i,j)*v j
  unfold paint; simp only [dif_pos, map_sum,map_smul,which,map_sum,map_smul,unitPaint,smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp [cell_price,wedge]
  intro b _ hb; simp [Ne.symm hb]

set_option maxHeartbeats 250000 in
lemma gram_scoop {b:Buffer F d}(h:Frigid b)(he : 4≤ d)(hG:G.Simple) (t : ℝ): RG11.Rigidity.Gram sources (posed b t):=by
  let a := scoop (F:=F) he
  refine ⟨a,fun v c j=> if h : 0=j then v c • (h ▸ blade (0:Axis) 1 (1:ℝ)) else 0,fun v M=>?_⟩
  have ht : drive b.val a.v t=a.v := drive_anchor _ _ (h.four he hG _) _
  -- both slates realize THIS probe. Use the exact weight computation only, no
  -- claim that orientation also fixes clocks at nonzero coupling.
  have hp(A:Performer G (News F d))(hr:A.deadline a=a.n)(hb:canon (A.slate a)=writes F d a.v):
      A.data (a,(fun c j=> if h : 0=j then v c • (h ▸ blade (0:Axis) 1 (1:ℝ)) else 0)) M=‖grid M v‖^2:= by
    apply Complex.ofReal_injective
    rw [Performer.data,← prints_out,hr,← Reads.prints,hb]
    change probe _ (MvPolynomial.weightedHomogeneousComponent _ _ _)=_
    rw [MvPolynomial.weightedHomogeneousComponent_eq_self a.gr]; change probe (paint _ M) (writes F d (banner F he (0,1) (0,1)))=_; dsimp only; rw [banner_reads (F:=F) he,bloc_team,basicTeam,paint_cell v M,real_inner_self_eq_norm_sq]
  refine ⟨hp _ rfl (drawn _ a.base a.real|>.1),hp _ rfl ?_⟩
  exact (drawn (drive b.val a.v t) (directs b t _ a.price a.base) (drive_real b t _ a.real)).1.trans (congr_arg (writes F d) ht)

end YM.RG11.Rigidity.Ice
