import YM.Integration.WilsonSeparatedOriginalSlabTranslation
import YM.Integration.WilsonSeparatedOriginalProfileCentral

/-! All true child displacements use one centered relative address, an actual common integer translate on the ordinary chart of the three original smooth bodies. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabChildSites
open Function Finset Lattice Wilson RG Source RG05Readout RG05Readout.Native MergeProof
open scoped Classical BigOperators Topology
variable {G:Gauge}

def site {a f:Side}(A:Ratio a f)(o:Fin 3 → Site f)(c:Site f):Fin 3 → Site f:=
  WilsonSeparatedOriginalProfileAnchor.anchor A (fun i=>o i+c)
def offset {a f:Side}(A:Ratio a f)(o:Fin 3 → Site f)(c:Site f):Cover:=
  lift (A.residue (o 0+c))-lift (o 0)
def limit {a f:Side}(A:Ratio a f)(J:ℕ):ℕ:=A.count.val+2*J

theorem coded {a f:Side}(A:Ratio a f)(o:Fin 3 → Site f)(c:Site f)(i:Fin 3):
    site A o c i=wrap f (lift (o i)+offset A o c):=by
  have decomp:=A.unpack_at (o 0+c)
  change o i+c+A.root (-(A.parent (o 0+c)))=_
  rw [offset,map_neg,map_add,map_sub,wrap_lift,wrap_lift]
  change A.root (A.parent (o 0+c))+wrap f (lift (A.residue (o 0+c)))=o 0+c at decomp
  rw [show wrap f (lift (A.residue (o 0+c)))=(o 0+c)-A.root (A.parent (o 0+c)) from (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans decomp)]
  abel

theorem centered {a f:Side}(A:Ratio a f)(o:Fin 3 → Site f)(c:Site f):
    A.parent (site A o c 0)=0 ∧ (∀i k,separation (site A o c i) (site A o c k)=separation (o i) (o k)):=by
  obtain ⟨home,_,_,span⟩:=WilsonSeparatedOriginalProfileAnchor.located A (fun i=>o i+c)
  exact ⟨home,fun i k=>(span i k).trans (separation_translate ..)⟩

theorem chart {a f:Side}(A:Ratio a f)(o:Fin 3 → Site f)(c:Site f)(J:ℕ)
    (bound:∀i,separation (o i) 0 ≤ J)(wrapFree:2*limit A J<f.val)(i:Fin 3):
    lift (site A o c i)=lift (o i)+offset A o c ∧ separation (site A o c i) 0 ≤ limit A J:=by
  have inside (k:Axis):-(limit A J:ℤ) ≤ (lift (o i)+offset A o c) k ∧
      (lift (o i)+offset A o c) k ≤ (limit A J:ℤ):=by
    have ip:=component_le (o i) k
    have zp:=component_le (o 0) k
    have a:=bound i
    have b:=bound 0
    simp only [separation,sub_zero] at a b
    have d:=lift_centers (A.residue (o 0+c)) k
    simp only [offset,Pi.add_apply,Pi.sub_apply,limit,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat];constructor <;> omega
  have same:lift (site A o c i)=lift (o i)+offset A o c:=by
    apply lift_eq_iff.mpr;refine ⟨coded A o c i,?_⟩;intro k;have room:=inside k;constructor <;> omega
  refine ⟨same,?_⟩
  simp only [separation,sub_zero,pdist,same,Finset.sup_le_iff]
  intro k _;have room:=inside k;omega

private theorem grid (S:Schedule)(n:ℕ)(x y:Cover):S.gridPoint n (x+y)=S.gridPoint n x+S.gridPoint n y:=by
  apply PiLp.ext;intro k;simp [Schedule.gridPoint,mul_add]

theorem admitted (C:Family G){n per J:ℕ}{a:Side}(A:Ratio a (C.side n per))(o:Fin 3 → Site (C.side n per))
    (c:Site (C.side n per))(present:o∈Pulse.area (C:=C) (b:=n) (p:=per) J)(room:2*limit A J<(C.side n per).val)
    {η:ℝ}{F:Fin 3 → Body}(purchased:Pulse.buy C n per o η F):
    site A o c∈Pulse.area (C:=C) (p:=per) (b:=n) (limit A J) ∧ Pulse.buy C n per (site A o c) η F:=by
  have range:∀i,separation (o i) 0 ≤ J:=by simpa only [Pulse.area,Finset.mem_filter,mem_univ,true_and] using present
  have moved:=chart A o c J range room
  refine ⟨by simpa only [Pulse.area,Finset.mem_filter,mem_univ,true_and] using fun i=>(moved i).2,?_⟩
  intro i k ne x hx y hy
  have prior:=purchased i k ne x hx y hy
  simp only [Function.comp_apply,(moved _).1,grid]
  simpa only [Function.comp_apply,show ∀(x y z w d:E4),(x+d+z)-(y+d+w)=(x+z)-(y+w) from fun _ _ _ _ _=>by abel] using prior

end YM.Integration.WilsonSeparatedOriginalSlabChildSites
