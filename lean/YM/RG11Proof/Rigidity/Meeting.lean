import YM.RG11Proof.Rigidity.Crowd

/-!
# Collision recognition via bilocal production

First step. Keep the kernel's angular numerator as a real quadratic, keep
all Wick terms regular etc. Double contraction not interpreted separately on
the diagonal. Work in words with distinguished occurrences.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Tensor Analysis Maxwell Maxwell.Free Extra.FD.SphereTest Filter Set Function
open scoped BigOperators Topology ContDiff Classical
open Crowd
variable {G : Gauge}

def splitP (a b : Pig G) (L : Word G) := pulls L
    (fun c p=> line a c * meter (b::p))
def splitR (a b c : Pig G) (L : Word G) := pulls L (fun d p=> line a d * pulls p
    (fun e q=> line a e * meter (b::c::q)))

lemma pair_split (a b : Pig G) (L : Word G) : meter (a::b::L)=line a b * meter L + splitP a b L := by
  rw [meter,pair_step,pulls_cons]; rfl

/-- Key combinatorial identity (two identical local factors at the first
assay; arbitrary pair at the second). -/
lemma four_split (a b c : Pig G) (L : Word G) :
    meter (a::a::b::c::L)=
      2*line a b*line a c*meter L +
      2*line a b*splitP a c L + 2*line a c*splitP a b L + splitR a b c L := by
  simp_rw [pair_step (line) a,pulls_cons,show line a a = 0 from if_pos rfl,zero_mul,zero_add]
  unfold meter
  -- pair_step repeatedly (first both as list order). 
  simp_rw [pair_step (line) a,pulls_cons]
  simp_rw [mul_add,pulls_add]
  simp_rw [show ∀ d (q:List (Pig G)), line a d * (line a b * pairCost line (c::q))=
      line a b*(line a d * pairCost line (c::q)) from fun _ _=>mul_left_comm ..,
    show ∀ d (q:List (Pig G)), line a d * (line a c * pairCost line (b::q))=
      line a c*(line a d * pairCost line (b::q)) from fun _ _=>mul_left_comm ..,
    pulls_mul _ (fun d p=> line a d * pairCost line (c::p)) (line a b),
    pulls_mul _ (fun d p=> line a d * pairCost line (b::p)) (line a c)]
  unfold splitP splitR meter; ring

def same (y : E4) (a b : Foil) : Panel := ((a,y),b,y)

def splitAt (W : Crowd G) (y z : E4) (a b : Foil) :=
    ∑ c : G.ColorIndex, W.asks (splitP (toss a y c) (toss b z c))

def coldAt (W : Crowd G) (y z : E4) (a b c : Foil) :=
    ∑ s : G.ColorIndex, ∑ t : G.ColorIndex, W.asks (splitR (toss a y s) (toss b z t) (toss c z t))

lemma profile_split {W : Crowd G} (hw : W.asks meter=0) (a b : Foil) (y z : E4) :
    (panel W ((a,y),b,z)).asks meter=splitAt W y z a b := by
  rw [panelRead]; unfold splitAt
  refine Finset.sum_congr rfl fun i _=> ?_
  change W.asks (fun L=> meter (toss a y i::toss b z i::L))=_
  simp_rw [pair_split,ask_add,ask_mul,hw,mul_zero,zero_add]

lemma profile_cold {W : Crowd G} (hw : W.asks meter=0) (a b c : Foil) (y z : E4) :
    ((panel W (same z b c)).panel (same y a a)).asks meter =
      2*beam (y-z) a b*splitAt W y z a c + 2*beam (y-z) a c*splitAt W y z a b + coldAt W y z a b c := by
  simp_rw [panelRead]
  change (∑ i : G.ColorIndex, ∑ j : G.ColorIndex, W.asks (fun L=>meter (toss a y i::toss a y i::toss b z j::toss c z j::L))) = _
  simp_rw [fun i j => fun L : List (Pig G) => four_split (toss a y i) (toss b z j) (toss c z j) L,ask_add,ask_mul,hw,mul_zero,zero_add,toss_line,Finset.sum_add_distrib]
  unfold splitAt coldAt
  congr 1; congr 1 <;> {
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    simp [mul_ite,ite_mul] }

variable {S : Finset E4}
def bare (z : E4) (S : Finset E4) := {x : E4| z+x∉S}
lemma naked {z : E4} (h : z∉S) : bare z S ∈ 𝓝 0 := by
  suffices IsOpen (bare z S) from this.mem_nhds (by simpa [bare])
  exact S.finite_toSet.isClosed.isOpen_compl.preimage (continuous_const.add continuous_id)

lemma split_ghost {W : Crowd G} (h : W.Live S) (a b : Foil) (z : E4) :
    Ghost (bare z S) (fun x => splitAt W (z+x) z a b) := by
  unfold splitAt; apply Ghost.sumG; intro c _; unfold splitP pulls; apply ask_ghost; intro w hw
  apply Ghost.sumG; intro i hi
  let d : Pig G := w.2.get i
  have hd : d∈ w.2:= List.get_mem ..
  apply Ghost.mulG ((ghost_line z a c d).mono ?_)
  exact fun x hx he=> hx ((he : z+x = d.origin).symm ▸ h w hw d hd)

lemma cold_diff {W : Crowd G} (h : W.Live S) (a b c : Foil) {z : E4} (he : z∉S) :
    ContDiffAt ℝ ω (fun x=> coldAt W (z+x) z a b c) 0 := by
  have ht : 0∈ bare z S := by simpa [bare]
  unfold coldAt; apply ContDiffAt.sum; intro r _; apply ContDiffAt.sum; intro R _
  unfold splitR pulls; apply ask_diff; intro w hw
  have hh (d : Pig G) (hd : d∈ w.2) : ContDiffAt ℝ ω (fun x=> line (toss a (z+x) r) d) 0 :=
    (ghost_line z _ _ _).thin _ (by
      change z+0≠d.origin
      intro hk; exact he (((zero_add z).symm.trans ((add_comm 0 z).trans hk)).symm ▸ h w hw d hd))
  apply ContDiffAt.sum; intro i _; apply (hh _ (List.get_mem ..)).mul
  apply ContDiffAt.sum; intro j _; apply (hh _ ?_).mul contDiffAt_const
  exact List.mem_of_mem_eraseIdx (List.get_mem ..)

end YM.RG11.Rigidity
