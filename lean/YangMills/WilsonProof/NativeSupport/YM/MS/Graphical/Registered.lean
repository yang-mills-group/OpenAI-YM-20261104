import YM.MS.Graphical.Registered
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.IntegratePins

/-!
# Certificates for pin graph workers

Essentially a `Lift` that works on *all* time rather than just a fixed log-time.
The final identification will use it only at finite IR length, then on the
Laurent constant term send the IR regulator away.
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval
variable {I : Type} {K : Set ℂ} {t v u w a b c R r : ℝ} {m n : ℕ} {q k j : ℤ} {G : Gauge} {x : Tone.QP}
variable {F H : Schedule G} {z : ℂ}

def Short (R : ℝ): Prop := 0<R ∧ disc R ⊆ Town ∧ R ≤ 1
lemma Short.less (h : Short R) (hp : 0<r) (hv : r ≤ R) : Short r := ⟨ hp,(ball_subset_ball hv).trans h.2.1,hv.trans h.2.2⟩
lemma shortening {p q : ℝ} (hp : 0<p) (hq : 0<q) : ∃ r:ℝ,Short r ∧ r ≤ p ∧ r≤q := by
  obtain ⟨R,hR,hr⟩ := Metric.mem_nhds_iff.mp (way.mem_nhds (show (0:ℂ)∈Town by simpa using Town_nat 0))
  let r := min (min R 1) (min p q); have hk:r≤ min R 1:= min_le_left ..; have hv:r≤ min p q:= min_le_right ..
  exact ⟨r,⟨lt_min (lt_min hR zero_lt_one) (lt_min hp hq),(ball_subset_ball (hk.trans (min_le_left ..))).trans hr,hk.trans (min_le_right ..)⟩,hv.trans (min_le_left ..),hv.trans (min_le_right ..)⟩

def TimeEq (F H : Schedule G) := ∀ᶠ z in dotty, ∀ t, F t z = H t z

/-- The common-radius representative itself. `q` bounds field-leg rank, not an
analytic decay index. -/
structure AtPin (R : ℝ) (q : ℤ) (F : Schedule G) : Prop where
  analytic (t : ℝ): Hol (disc R) (F t)
  borel : ∀ z∈ disc R, BorelRow fun t => F t z
  capacity (t : ℝ) (z : ℂ) : z∈disc R → Issue q (F t z)
  fine : ∀ t, ∀ z∈disc R, Form0 false (F t z)

abbrev While (rapid : Bool) (R : ℝ) (F : Schedule G) : Prop :=
  if rapid then InPins R F else Subponential R F
abbrev PinPrice (rapid : Bool) (R : ℝ) (q : ℤ) (F : Schedule G) : Prop := AtPin R q F ∧ While rapid R F

/-- Uniform-*time* regulator representative: the `Eventually` in `TimeEq` is
**outside** the time quantifier. -/
def Countered (rapid : Bool) (q : ℤ) (F : Schedule G) :=
    ∃ r:ℝ, ∃ H, Short r ∧ TimeEq F H ∧ PinPrice rapid r q H

lemma Pays.narrows (h : Pays R F a) (hp : r≤ R) : Pays r F a :=
  fun I t Z B hv K HK hK hz=> h I t Z B hv K HK (hK.trans (ball_subset_ball hp)) hz
lemma Pays.zero' (G : Gauge) (R a : ℝ) : Pays R (0:Schedule G) a := by
  intro I t Z B hv K HK hK h
  simp only [Pi.zero_apply, ← cert,map_zero]; exact fall_zero fun i=> (exp_pos _).le
lemma Pays.add (h : Pays R F a) (he : Pays R H a) : Pays R (F+H) a := by
  intro I t Z B hv K HK hK hz; simp_rw [Pi.add_apply,← cert,map_add];
  exact fall_add (h I t Z B hv K HK hK hz) (he I t Z B hv K HK hK hz)
lemma TimeEq.refl (F : Schedule G) : TimeEq F F:= Eventually.of_forall (fun _ _=>rfl)
lemma TimeEq.symm (h : TimeEq F H) : TimeEq H F:= h.mono fun _ hz t=> (hz t).symm
lemma TimeEq.trans' {X : Schedule G} (h : TimeEq F H) (hp : TimeEq H X) : TimeEq F X:=
  (h.and hp).mono fun _ hz t=> (hz.1 t).trans (hz.2 t)
lemma TimeEq.add {X Y : Schedule G} (h : TimeEq F X) (he : TimeEq H Y) : TimeEq (F+H) (X+Y):=
  (h.and he).mono fun _ hz t=> congr_arg₂ (·+·) (hz.1 t) (hz.2 t)

lemma AtPin.resize (h : AtPin R q F) (hp : r≤ R) (hq : q ≤ k) : AtPin r k F:=
  let H := ball_subset_ball (x:=(0:ℂ)) hp
  ⟨fun t=> (h.analytic t).mono H, fun _ hz=>h.borel _ (H hz),fun t _ hz m=> (h.capacity t _ (H hz) m).up hq, fun t _ hz=>h.fine t _ (H hz)⟩
lemma AtPin.zero' (G : Gauge) (R : ℝ) (q : ℤ) : AtPin R q (0:Schedule G) :=
  ⟨fun _=>Hol.zero, fun _ _ _ _=>measurable_const, fun _ _ _ _ _ _=>rfl,fun _ _ _=>Form0.zero⟩
lemma AtPin.add (h : AtPin R q F) (he : AtPin R q H) : AtPin R q (F+H) :=
  ⟨fun i=> Hol.add (h.analytic i) (he.analytic i),fun i hi m w=> (h.borel i hi m w).add (he.borel i hi m w),
   fun i z hz m=> Limit.add (h.capacity i z hz m) (he.capacity i z hz m), fun t z hz=>
     (h.fine t z hz).add (he.fine _ _ hz)⟩

lemma AtPin.Lift (h : AtPin R q F) (hp : TimeEq H F) (h0 : 0<R) (t : ℝ) :
    Lift (H t) (F t 0) := Lift.congr (Lift.trim (h.analytic t) h0) (hp.mono fun _ hz=>(hz t).symm)

variable {V : Bool}
lemma PinPrice.resize (h : PinPrice V R q F) (hp : r≤R) (hv : q≤k) : PinPrice V r k F := by
  obtain ⟨A,hA⟩:= h
  refine ⟨A.resize hp hv,?_⟩
  cases V; · exact let ⟨a,h⟩:= (show Subponential R F from hA); (show Subponential r F from ⟨ a,h.narrows hp ⟩)
  change InPins r F; exact fun a=> ((show InPins R F from hA) a).narrows hp

lemma PinPrice.add (h : PinPrice V R q F) (hp : PinPrice V R q H) : PinPrice V R q (F+H) := by
  refine ⟨AtPin.add h.1 hp.1,?_⟩
  cases V with
  | false=>
    obtain ⟨a,ha⟩:= show Subponential R F from h.2
    obtain ⟨b,hb⟩:= show Subponential R H from hp.2
    exact show Subponential R (F+H) from ⟨_, (ha.more (min_le_left a b)).add (hb.more (min_le_right ..))⟩
  | true=>
    exact show InPins R (F+H) from fun a=> ((show InPins R F from h.2) a).add ((show InPins R H from hp.2) a)
lemma PinPrice.zero' (G : Gauge) (R : ℝ) (q : ℤ) (b : Bool) : PinPrice b R q (0:Schedule G) := by
  refine ⟨AtPin.zero' ..,?_⟩
  cases b
  · exact show Subponential _ _ from ⟨0,Pays.zero' G R 0⟩
  exact show InPins _ _ from fun a=> Pays.zero' G R a


lemma TimeEq.close (F : Schedule G) (h : TimeEq F H) (y : ℝ) : TimeEq (closeAt y F) (closeAt y H):=
  h.mono fun z hz t=> congr_arg (radialClose (halfD t) z y) (hz t)
lemma TimeEq.tree {X Y : Schedule G} (h : TimeEq F X) (he : TimeEq H Y) : TimeEq (treeAt F H) (treeAt X Y):=
  (h.and he).mono fun _ hz t=> congr_arg₂ (bridging t) (hz.1 t) (hz.2 t)
lemma TimeEq.joins (x : Tone.QP) (y : ℝ) {X Y : Schedule G} (h : TimeEq F X) (he : TimeEq H Y) : TimeEq (joinAt x y F H) (joinAt x y X Y):=
  (h.and he).mono fun z hz t=> congr_arg₂ (wickJoin x (halfD t) z y) (hz.1 t) (hz.2 t)
lemma TimeEq.integrate (h : TimeEq F H) : TimeEq (integratePins F) (integratePins H):=
  h.mono fun z hz t=> congr_arg (fun v=> mend v t) (show (fun s=>F s z)=_ from funext hz)

lemma halfDK (s : ℝ) : Knot false (halfD (G:=G) s):= by rw [halfD_eq]; exact c_bo s

namespace AtPin
lemma close (h : AtPin R q F) (hs : Short R) (y : ℝ) : AtPin R (q-2) (closeAt y F) :=
  ⟨fun t=>radial_hol (halfDK t) hs.2.1 isOpen_ball (h.analytic t) (fun z hz=>(h.fine t z hz).token) y,
   fun z hz=> radial_meas (h.borel z hz) (fun t=>(h.fine t z hz).price) z y,
   fun t z hz=> radial_issue (hs.2.1 hz) (halfDK t) (h.fine t z hz) (h.capacity t z hz) y,
   fun t z hz=> radialForm (hs.2.1 hz) (halfDK t) (h.fine t z hz) y⟩
lemma tree (h : AtPin R q F) (hp : AtPin R k H) : AtPin R (q+k-2) (treeAt F H) := by
  have he i z:= bridging_eq i (F i z) (H i z);
  unfold treeAt; refine ⟨fun t=>?_,fun z hz=>bridge_meas (h.borel _ hz) (hp.borel _ hz),?_,?_⟩
  · simp_rw [he]; exact Hol.woods (h.analytic t) (hp.analytic t) (Hop.crate (c_bo (G:=G) (b:=false) t).price)
  · intro t z hz; rw [he]; exact whole (reverse_a G t) (h.capacity t z hz) (hp.capacity t z hz)
  intro t z hz; rw [he]; exact Form0.treed (c_bo t) (cl_a G t) (reverse_a G t) (h.fine t z hz) (hp.fine t z hz)
lemma joined (x : Tone.QP) (y : ℝ) (h : AtPin R q F) (hp : AtPin R k H) (hs : Short R) :
    AtPin R (q+k-2) (joinAt x y F H) := by
  refine ⟨fun t=> wickJoin_hol x y hs.2.1 isOpen_ball (h.analytic t)
      (fun z hz=>(h.fine t z hz).token) (hp.analytic t) (fun z hz=> (hp.fine t z hz).token) (halfDK t),
    ?_,fun t z hz=> wickJoin_issue x y (h.fine t z hz) (h.capacity t z hz) (hp.fine t z hz)
       (hp.capacity _ _ hz) (hs.2.1 hz) (halfDK t),
     fun t z hz=> wickJoin_form x y (h.fine _ _ hz) (hp.fine _ _ hz) (hs.2.1 hz) (halfDK t)⟩
  intro z hz
  obtain he:= h.borel z hz; obtain hm:= hp.borel z hz; have ht i:=bring_form x (h.fine i z hz)
  exact fun m l=> ((radial_meas (shuffle_meas (bring_meas (x:=x) he) hm) (fun t=> (shuffle_form (ht t) (hp.fine t z hz)).price) z y m l).sub (shuffle_meas
     (radial_meas (bring_meas he) (fun t=>(ht t).price) z y) hm m l)).sub
     (shuffle_meas (bring_meas (x:=x) he) (radial_meas hm (fun t=>(hp.fine t z hz).price) z y) m l)

lemma integrated (h : AtPin R q F) (hp : Pays R F a) (hv : 0<a) : AtPin R q (integratePins F) := by
  obtain hx:= integrate_hol hp hv h.borel h.analytic
  refine ⟨hx,fun z hz=> integrate_meas h.borel hz,fun t z hz=>?_,fun t z hz=>⟨ (hx t).link hz isOpen_ball,?_⟩⟩
  · exact need_tail.runner (u:=fun x=>F x z) t (pinGather hp hv h.borel hz t) (fun i=> h.capacity i z hz)
  exact need_true.runner (u:=fun x=> F x z) t (pinGather hp hv h.borel hz t) (fun i=>(h.fine i z hz).token)
end AtPin
end YM.MS.Graphical
