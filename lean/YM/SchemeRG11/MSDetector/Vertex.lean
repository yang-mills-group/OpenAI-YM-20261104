import YM.SchemeRG11.MSDetector.Frost

/-!
Read at four, integrate by linearity even at unequal cutoff parametrization.
Orbit representation: anchor order of the three marks `(z,x,y)`, apex
choice `s` of V3 fixes cycle that carries input Color to that anchor. `B`
connects opt curvature derivative of V3 there, `C,D` the two A's. -/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.SchemeRG11.MSDetector
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm Flare Asymptotics
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4

variable (μ : ℝ) (R : ℝ) (I J K : Gem) (X : Tri)
def wheel : ℂ:= street (roll I J K fun l m n=> MSDetector.star μ R ((sumBits l m n).map atEye) 0 X)
/-- One curvature completion in orientation (Kexternal i, then A to j, A to k). Assignments to axes
ordered FIRST, after summing both Wick choices their antisymmetrized tensor
makes terms equal, cancel 1/2. No factor 2 here. Other assignments counted
separately IF PRESENT (a C_x pot not landing at y).
-/
def core (z x y:E4):= ∑ a:Axis,∑ b:Axis,(coin I a b:ℂ)*near μ R J a (x-z)*near μ R K b (y-z)

variable {μ R X}
include I J K
lemma scene (hμ:0<μ)(hx:X∈clearance 4): ContinuousAt (wheel μ R I J K) X := by
  unfold wheel street
  let U l m n (x:Tri):= MSDetector.star μ R ((sumBits l m n).map atEye) 0 x
  let T x:= roll I J K (fun l m n=> U l m n x)
  have hi l m n : ContinuousAt (U l m n) X:= by unfold U MSDetector.star weigh; exact tendsto_finsetSum Finset.univ fun i _=> tendsto_const_nhds.smul (tendsto_finsetSum Finset.univ fun j _=> tendsto_const_nhds.smul (tendsto_finsetSum Finset.univ fun k _=> tendsto_const_nhds.smul (walks hμ _ hx)))
  have hp (s a b c d) : ContinuousAt (fun x=> T x s a b c d) X := by
    exact tendsto_finsetSum Finset.univ (fun y _=> tendsto_finsetSum Finset.univ fun z _=> tendsto_finsetSum Finset.univ fun i _=> tendsto_const_nhds.smul (hi ..))
  have hh (a b c d) : ContinuousAt (fun x=> strum (T x) a b c d) X:= ((hp ..).add (hp ..)).add (hp ..)
  exact tendsto_finsetSum Finset.univ (fun a _=> tendsto_finsetSum Finset.univ fun b _ => (hh ..).sub (hh ..))

variable {ι : Type} {v : Filter ι} [v.IsCountablyGenerated] {r : ι→ℝ} (hr : Tendsto r v atTop) {x : ι→Tri} (hx:X∈clearance 4) (h : Tendsto x v (𝓝 X))
include h hx hr
lemma gate (hμ : 0<μ): Tendsto (fun i=> wheel μ (r i) I J K (x i)) v (𝓝 (Complex.ofReal (street (Crew I J K X)))) := by
  let F i l m n:= MSDetector.star μ (r i) ((sumBits l m n).map atEye) 0 (x i)
  let T i:= roll I J K (F i)
  have hh l m n:Tendsto (fun i=> F i l m n) v (𝓝 (Complex.ofReal (yolk l m n X))) := by rw [yolks _ _ _ μ]; exact lifted (fun i=> lifted (fun j=> lifted fun k=> rolling hμ _ hx (ends i hr) (ends j hr) (ends k hr) h))
  let D:= Crew I J K X
  have hu (s a b c d) : Tendsto (fun i=> T i s a b c d) v (𝓝 (Complex.ofReal (D s a b c d))) := by
     unfold D T Crew roll; simp only [Complex.ofReal_sum]
     refine tendsto_finsetSum Finset.univ fun _ _=> tendsto_finsetSum Finset.univ fun _ _=> tendsto_finsetSum Finset.univ fun z _=> ?_
     rw [← Complex.ofRealCLM_apply,Complex.ofRealCLM.map_smul]; exact tendsto_const_nhds.smul (hh ..)
  have hv (a b c d) : Tendsto (fun i=> strum (T i) a b c d) v (𝓝 (Complex.ofReal (strum D a b c d))) := by
    unfold strum; push_cast; exact ((hu ..).add (hu ..)).add (hu ..)
  unfold street wheel; push_cast; exact tendsto_finsetSum Finset.univ fun a _=> tendsto_finsetSum Finset.univ fun b _=> (hv ..).sub (hv ..)
omit h hx
lemma lid (μ : ℝ){x y z : ι→E4} {u v' w:E4}(hz:Tendsto z v (𝓝 u)) (hp:Tendsto x v (𝓝 v'))(hk:Tendsto y v (𝓝 w))(h:u≠v')(he:u≠w):
    Tendsto (fun i=> core μ (r i) I J K (z i) (x i) (y i)) v (𝓝 (Complex.ofReal (pileup I J K v' w u))) := by
  unfold core pileup; push_cast
  exact tendsto_finsetSum Finset.univ (fun a _=> tendsto_finsetSum Finset.univ fun b _=> (tendsto_const_nhds.mul (near_go _ _ _ hr (hp.sub hz) (sub_ne_zero.mpr h.symm))).mul (near_go _ _ _ hr (hk.sub hz) (sub_ne_zero.mpr he.symm)))

omit hr in
lemma perched (hμ : 0<μ){Y : Type}[TopologicalSpace Y]{x y z:Y→E4}{v:Y} (hx:ContinuousAt x v)(hy:ContinuousAt y v)(hz:ContinuousAt z v)(h:z v≠x v)(hh:z v≠y v):
    ContinuousAt (fun u=> core μ R I J K (z u) (x u) (y u)) v := by
  unfold core; refine tendsto_finsetSum Finset.univ (fun a _=> tendsto_finsetSum Finset.univ fun b _=> ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_)
  · exact (near_o hμ R J a (sub_ne_zero.mpr h.symm)).comp (f:=fun u=> x u-z u) (hx.sub hz)
  exact (near_o hμ R K b (sub_ne_zero.mpr hh.symm)).comp (f:=fun u=>y u-z u) (hy.sub hz)
end YM.SchemeRG11.MSDetector
