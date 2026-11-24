import YM.Integration.WilsonAddressedPublicPairFence
import YM.Integration.WilsonAddressedPublicNamedQuadrature
import YM.Integration.WilsonOriginalPublicRelativeGramAddresses
import YM.GapsContact.Slab.VacGram

/-! Read the reflected card of one enrolled original source on the continuum detector
at any separation beyond its actual width. The cutoff limits precede the auxiliary grid limit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace YM.Integration.WilsonMeasuredPublicEntranceCardDetector
open Function Filter Finset Set Lattice Wilson RG Source Cells Extraction Spec Table Climb
open PhysicalNext.Repeat.Legato GapsContact Next.Rank Maxwell
open Trace.Pilot Trace.Terrace GapsContact.Ascent Push.FiniteDetection.Free Push.FiniteDetection.Kelvin
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicSelfCards (fee width)
open WilsonAddressedPublicNamedQuadrature (value physical_limit)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{r:ℝ}(B:Book F (l:=l) H z D T r)(d:Fin (D+1))(v:S.Field d.val)(b:Bool)
local notation "C" => R.family

theorem grid (cash:PostT ((C).path.levels))(below:(l:Filter (ℕ×ℕ))≤f.fuse)
    (site:ℕ)(o:Fin 2→ Cover)(safe:Extraction.Order.grid C site o∈generic 2)
    (live:0<width F B d v b)(near:‖(C).S.gridPoint site (o 0-o 1)‖≤1)
    (far:2*(C).S.a (width F B d v b-1)<‖(C).S.gridPoint site (o 0)-(C).S.gridPoint site (o 1)‖)(ax:Axis):
    ‖value R F (fun _:Fin 2=>d) (fun _=>v) ax site o‖≤(fee F B d v b)^2:=by
  classical
  let book:=fun _:Bool=>B
  let vec:=fun (_:Bool) (_:Unit)=>v
  let br:=fun (_:Bool) (_:Unit)=>b
  let loc:=fun _:Unit=>o
  let coin:=fun _:Unit=>(1:ℂ)
  have sale:=WilsonAddressedPublicPairFence.original R F book d vec br cash false () () site loc coin
    (by simpa [WilsonAddressedPublicPairPins.whenFiled,book,vec,br] using live)
    (fun _=>near) (fun _=>by simpa [WilsonAddressedPublicPairPins.whenFiled,book,vec,br,loc] using far)
  have lim:=physical_limit R F (fun _:Fin 2=>B) (fun _=>d) (fun _=>v) (fun _=>b) ax site loc coin below (fun _=>safe)
  have paid:=le_of_tendsto lim.norm ((sale.filter_mono below).mono (fun w got=>got ax))
  simpa [coin,loc,book,br,vec,WilsonAddressedPublicPairPins.cost,pow_two] using paid

def pair (ax:Axis)(x:Points 2):ℂ:=S.classMoment S (fun _:Fin 2=>d.val) x ![S.adj F.room.kernel.spin d.val ax v,v]

theorem continuum (cash:PostT ((C).path.levels))(below:(l:Filter (ℕ×ℕ))≤f.fuse)
    (x:Points 2)(clear:x∈conf 2)(live:0<width F B d v b)
    (near:‖x 0-x 1‖<1)(far:2*(C).S.a (width F B d v b-1)<‖x 0-x 1‖)(ax:Axis):
    ‖pair R F d v ax x‖≤(fee F B d v b)^2:=by
  let o:=fun j=>ports R ∅ x j 1
  let y:=fun j=>Extraction.Order.grid C j (o j)
  have limit:Tendsto y atTop (𝓝 x):=by
    have hit:=WilsonOriginalPublicRelativeGramAddresses.limit (n:=2) ∅ x (δ:=(C).S.a)
      (Eventually.of_forall (C).S.a_pos) (C).S.shrinks
    simpa only [y,o,WilsonOriginalPublicRelativeGramAddresses.placed R ∅ x _ one_pos,div_one,one_smul] using hit
  let coords:=PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 2=>E4)
  have each:=tendsto_pi_nhds.mp ((coords.continuous.tendsto x).comp limit)
  have metric:Tendsto (fun j=>‖y j 0-y j 1‖) atTop (𝓝 ‖x 0-x 1‖):=((each 0).sub (each 1)).norm
  have cont:ContinuousAt (pair R F d v ax) x:=by
    exact ((S.class_smooth S F.room.kernel.smooth
      (fun i:Fin 2=>(⟨d.val,(![S.adj F.room.kernel.spin d.val ax v,v]:Fin 2→S.Field d.val) i⟩:S.Tag))).continuousOn.continuousAt
        ((conf_open _).mem_nhds clear))
  apply le_of_tendsto ((cont.tendsto.comp limit).norm)
  filter_upwards [metric.eventually_lt_const near,metric.eventually (lt_mem_nhds far)] with j top bot
  have p:=grid R F B d v b cash below j (o j) (WilsonOriginalPublicRelativeGramAddresses.screened R ∅ x j one_pos) live
    (by rw [Frontier6.Road.grid_sub R.family];exact top.le) bot ax
  have equal:value R F (fun _:Fin 2=>d) (fun _=>v) ax j (o j)=pair R F d v ax (y j):=by
    let ds:=WilsonOriginalBlissMixedGram.grades d.val d.val
    let row:(i:Fin 2)→S.Field (ds i):=Fin.cons (α:=fun i=>S.Field (ds i)) (S.adj F.room.kernel.spin d.val ax v) (fun _=>v)
    let one:Fin 2→S.Tag:=fun i=>⟨ds i,row i⟩
    let two:Fin 2→S.Tag:=fun i=>⟨d.val,(![S.adj F.room.kernel.spin d.val ax v,v]:Fin 2→S.Field d.val) i⟩
    have eq:one=two:=by funext i;fin_cases i <;> rfl
    exact congrArg (S.useAt S (y j)) eq
  simpa only [equal,Function.comp_apply] using p

theorem original (cash:PostT ((C).path.levels))(below:(l:Filter (ℕ×ℕ))≤f.fuse)
    (live:0<width F B d v b){τ:ℝ}(pos:0<τ)(small:τ<1)(apart:2*(C).S.a (width F B d v b-1)<τ)
    (nonnegative:0≤fee F B d v b):cost F d.val τ v≤fee F B d v b:=by
  let σ:=Equiv.swap (0:Fin 2) 1
  let x:=τ • detectors
  have cleared:x∈conf 2:=Work.A05.smul_conf pos detectors_in
  let y:=Points.rearrange σ x
  have dist:‖y 0-y 1‖=τ:=by
    change ‖τ • detectors.ofLp (σ 0)-τ • detectors.ofLp (σ 1)‖=τ
    simp [σ,detectors,pole,norm_smul,abs_of_pos pos]
  have measured:=continuum R F B d v b cash below y (Points.rearrange_in σ cleared) live (dist.trans_lt small) (apart.trans_eq dist.symm) timeAxis
  have swapped:(![S.adj F.room.kernel.spin d.val timeAxis v,v]:Fin 2→S.Field d.val)=
      ![v,flipField F d.val v] ∘ σ:=by
    funext i;fin_cases i <;> simp [σ,Table.adj,flipField]
  have exactRead:pair R F d v timeAxis y = valTwo S d.val x v (flipField F d.val v):=by
    unfold pair valTwo
    rw [swapped]
    exact F.room.kernel.laws.toSymmetric.same σ cleared
      (fun i:Fin 2=>(⟨d.val,S.representative d.val (![v,flipField F d.val v] i)⟩:(C).book.Token))
  rw [exactRead] at measured
  exact (Real.sqrt_le_sqrt measured).trans_eq (Real.sqrt_sq nonnegative)

theorem reflected (cash:PostT ((C).path.levels))(below:(l:Filter (ℕ×ℕ))≤f.fuse)
    (live:0<width F B d v b){τ:ℝ}(pos:0<τ)(small:τ<1)(apart:2*(C).S.a (width F B d v b-1)<τ)
    (nonnegative:0≤fee F B d v b):
    cost F d.val τ (S.adj F.room.kernel.spin d.val timeAxis v)≤fee F B d v b:=by
  let x:=τ • detectors
  have clear:x∈conf 2:=Work.A05.smul_conf pos detectors_in
  have dist:‖x 0-x 1‖=τ:=by
    change ‖τ • detectors.ofLp 0-τ • detectors.ofLp 1‖=τ
    simp [detectors,pole,norm_smul,abs_of_pos pos]
  have paid:=continuum R F B d v b cash below x clear live (dist.trans_lt small) (apart.trans_eq dist.symm) timeAxis
  have square:flipField F d.val (S.adj F.room.kernel.spin d.val timeAxis v)=v:=by
    exact S.reflect_twice F.room.kernel.spin d.val timeAxis v
  unfold cost
  rw [square]
  exact (Real.sqrt_le_sqrt paid).trans_eq (Real.sqrt_sq nonnegative)

end YM.Integration.WilsonMeasuredPublicEntranceCardDetector
end
