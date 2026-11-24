import YM.Integration.WilsonSeparatedPositionCameras
import YM.Integration.WilsonSeparatedTubeCoordinates

/-! A common complex radius for a separated finite Euclidean roster with arbitrary
diameter. The original rotation estimate separates all normalized pair directions. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkTubeRoom
open Function Filter Set Metric Boundary Boundary.Surface GapsContact GapsContact.Tunnel
open WilsonSeparatedPositionCameras WilsonSeparatedTubeCoordinates
open scoped Classical Topology
variable {n:ℕ}

private def edge (z:Full n)(i j:Fin n):=shade z j-shade z i

private lemma small {δ:ℝ}(hp:0<δ):∃e:ℝ,0<e ∧ ∀z:Full n,‖z‖≤e→Room (shade z) (-δ):=by
  have note (i j:Fin n):∀ᶠz:Full n in 𝓝 0,-δ≤YM.time (edge z i j)-‖spatial (edge z i j)‖:=by
    let f(z:Full n):=YM.time (shade z j-shade z i)-‖spatial (shade z j-shade z i)‖
    have hc:Continuous f:=by dsimp [f];fun_prop
    have zero:shade (0:Full n)=0:=by
      apply Points.flatten.injective;ext a;simp [shade]
    have z:f 0=0:=by simp [f,zero]
    exact hc.continuousAt (le_mem_nhds (show -δ<f 0 by rw [z];exact neg_lt_zero.mpr hp))
  have all:∀ᶠz:Full n in 𝓝 0,∀i j,-δ≤YM.time (edge z i j)-‖spatial (edge z i j)‖:=
    eventually_all.mpr fun i=>eventually_all.mpr (note i)
  obtain ⟨e,ep,room⟩:=Metric.mem_nhds_iff.mp all
  refine ⟨e/2,half_pos ep,fun z hz i j _=>room ?_ i j⟩
  simpa only [mem_ball,dist_zero_right] using hz.trans_lt (half_lt_self ep)

private lemma plus {u v:Points n}{a b:ℝ}(hu:Room u a)(hv:Room v b):Room (u+v) (a+b):=by
  intro i j hi
  have h:=add_le_add (hu i j hi) (hv i j hi)
  change a+b≤YM.time ((u j+v j)-(u i+v i))-‖spatial ((u j+v j)-(u i+v i))‖
  rw [add_sub_add_comm,Mink.clock_add,Mink.rest_add]
  linarith only [h,norm_add_le (spatial (u j-u i)) (spatial (v j-v i))]

/-- The two points may lie in widely separated blocks. -/
theorem original {η:ℝ}(ep:0<η):
    ∃δ∈Ioc (0:ℝ) 1,∃ρ:ℝ,0<ρ ∧
    ∀x:Points n,(∀i j:Fin n,i≠j→η≤dist (x i) (x j))→
    ∃g:Ortho,∃σ:Equiv.Perm (Fin n),view g σ x∈ordered n ∧
      ∀z∈closedBall (embedding (coordinates (view g σ x))) ρ,Room (shade z) δ:=by
  obtain ⟨a,ap,probes⟩:=OPE.Coverage.directions (Fin n×Fin n)
  let δ:=min 1 (a*η/2)
  have dp:0<δ:=lt_min zero_lt_one (half_pos (mul_pos ap ep))
  obtain ⟨ρ,rp,minor⟩:=small (n:=n) dp
  refine ⟨δ,⟨dp,min_le_left ..⟩,ρ,rp,?_⟩
  intro x clear
  obtain ⟨g,hg⟩:=probes fun ij=>x ij.1-x ij.2
  let clock(i:Fin n):=YM.time (Ortho.move g (x i))
  have wage (i j:Fin n)(ne:i≠j):a*η≤|clock i-clock j|:=by
    have bound:=hg (i,j)
    change a*‖x i-x j‖≤|Ortho.move g (x i-x j) timeAxis| at bound
    rw [show Ortho.move g (x i-x j)=Ortho.move g (x i)-Ortho.move g (x j) from (Ortho.motion g).map_sub ..] at bound
    exact (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using clear i j ne) ap.le).trans bound
  let σ:=Tuple.sort clock
  have increasing:StrictMono (clock ∘ σ):=by
    apply (Tuple.monotone_sort _).strictMono_of_injective
    apply Function.Injective.comp _ σ.injective
    intro i j same
    by_contra neq
    have price:=wage i j neq
    rw [same,sub_self,abs_zero] at price
    exact (mul_pos ap ep).not_ge price
  refine ⟨g,σ,increasing,?_⟩
  let c:Full n:=embedding (coordinates (view g σ x))
  have margin:Room (shade c) (2*δ):=by
    change Room (shade (glow _ (dawn _))) _
    rw [im_glow]
    apply Room.of_broad
    intro i j hij
    have h:=wage (σ j) (σ i) (fun same=>hij.ne (σ.injective same).symm)
    have pos:clock (σ i)≤clock (σ j):=(increasing hij).le
    rw [abs_of_nonneg (sub_nonneg.mpr pos)] at h
    have limit:δ≤a*η/2:=min_le_right ..
    change 2*δ≤clock (σ j)-clock (σ i)
    linarith
  intro z hz
  have norm:‖z-c‖≤ρ:=by simpa only [←dist_eq_norm] using mem_closedBall.mp hz
  have eq:shade (c+(z-c))=shade c+shade (z-c):=by
    apply Points.flatten.injective;ext i;simp [shade]
  have together:=plus margin (minor (z-c) norm)
  rwa [←eq,add_sub_cancel,show 2*δ+-δ=δ by ring] at together

end YM.Integration.WilsonMovingForkTubeRoom
