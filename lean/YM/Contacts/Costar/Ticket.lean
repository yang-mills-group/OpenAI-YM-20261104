import YM.Work.B15
import YM.Work.B16
import YM.Work.B17
import YM.Work.B03
import YM.Work.B04
import YM.Work.B05
import YM.Next.UV_STRESS.Vary

/-!
# Trains on the same construction, subtail with possibly varying slot budget

Companion to B16 (adapted from it) exactly on its geometry and pos rels but uses a *subfilter* limit of the realized label field class. The same projection ties and positions are kept. Price exterior cells later in the replicas. A current in a ticket (unlike the base `Episode.current`) can here have linear combinations in the prescribed caps depending on both period and mesh without convergence outside the chosen subtails. This will allow costing point tests on every phase with identical constants to unselected.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Costar
open Function Set Filter MeasureTheory Extraction Wilson Spec Cells Lattice Word Bid Work.B16
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {F : Extraction.Order} {k b : ℕ}
variable (E : Episode C F k) (τ:Filter (ℕ×ℕ))
structure Ticket where
   current (i : Fin E.num) (j : Fin (E.image i)) (N p : ℕ) : C.label (E.weight i j)
   tends i j : Tendsto (fun x:ℕ×ℕ=> current i j x.1 x.2) τ (𝓝 (E.point i j))
namespace Ticket
variable {E τ}(T: Ticket E τ)

def cuts (N p) (u : Cover) (v : Config G (C.side N p)) := ∑ i, E.factor i * ∏ j,
    C.O N p (d:=E.weight i j) (T.current i j N p) (location C.S k N p (E.seats i j+u)) v
def twice (h : b≤k) (t m N p) (v : Config G (C.side N p)) := ∏ j : Fin (2*m),
    if j.val%2=0 then star (T.cuts N p (Episode.step C h t j.val) v) else T.cuts N p (Episode.step C h t j.val) v
def fromCut (h : b≤ k) (t m N p) := moment (C.beta N p) (T.twice h t m N p)
variable {m : ℕ} (i : Fin (2*m) → Fin E.num)
def onSlot (s : Slot E i) (N p : ℕ) : C.label (gradeSlot E i s) :=
  if s.1.val % 2 = 0 then star (T.current (i s.1) s.2 N p) else T.current (i s.1) s.2 N p


def onObs (e : b ≤ k) (t N p : ℕ) (U : Config G (C.side N p)) (s : Slot E i) :=
  C.O N p (d := gradeSlot E i s) (onSlot T i s N p) (location C.S k N p (placeSlot E i e t s)) U

def tick (e : b ≤ k) (t N p : ℕ) (U : Config G (C.side N p)) :=
  ∏ a, onObs T i e t N p U ((slots E i).get a)

lemma tick_cont (e : b ≤ k) (t N p : ℕ) : Continuous (tick T i e t N p) :=
  continuous_finsetProd _ fun _ _ => C.continuousO _ _ _ _ _

lemma twice_expand (H : C.Makes) (e : b ≤ k) (m t N p : ℕ) (hN : ∀ a q, C.ref (E.weight a q) ≤ N)
    (U : Config G (C.side N p)) : T.twice e t m N p U = ∑ i, E.price m i * tick T i e t N p U := by
  let factor (j : Fin (2*m)) (a : Fin E.num) := if j.val%2=0 then star (E.factor a) else E.factor a
  let monomial (j : Fin (2*m)) (a : Fin E.num) := ∏ q : Fin (E.image a),
    let v := if j.val%2=0 then star (T.current a q N p) else T.current a q N p
    C.O N p (d := E.weight a q) v (location C.S k N p (E.seats a q+Episode.step C e t j.val)) U
  have h (j : Fin (2*m)) :
      (if j.val%2=0 then star (T.cuts N p (Episode.step C e t j.val) U) else T.cuts N p (Episode.step C e t j.val) U) =
        ∑ a, factor j a * monomial j a := by
    by_cases hj : j.val%2=0
    · simp only [hj,if_true,Ticket.cuts,star_sum,star_mul',star_prod,factor,monomial]
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact Finset.prod_congr rfl fun q _ => (C.reality H (hN a q) _ _ _).symm
    simp only [hj, if_false, Ticket.cuts,factor,monomial]
  unfold Ticket.twice
  simp_rw [h]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.prod_mul_distrib,tick,slotProd]
  rfl

lemma fromCut_expand (H : C.Makes) (e : b ≤ k) (m t : ℕ) :
    ∀ᶠ c : ℕ × ℕ in F.fuse, T.fromCut e t m c.1 c.2 =
      ∑ i, E.price m i * moment (C.beta c.1 c.2) (tick T i e t c.1 c.2) := by
  have he : ∀ᶠ c : ℕ × ℕ in F.fuse, ∀ a q, C.ref (E.weight a q) ≤ c.1 :=
    eventually_all.mpr fun a => Extraction.Order.witnesses (C:=C) (fun q => ⟨_,E.point a q⟩) F
  filter_upwards [he] with c hN
  dsimp only [fromCut, moment]
  simp_rw [twice_expand T H e m t c.1 c.2 hN]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  exact fun i _ => continuous_integrable (C.beta c.1 c.2) (continuous_const.mul (tick_cont T i e t c.1 c.2))


section
variable [τ.NeBot](hT:τ≤F.fuse)
lemma on_limits (s:Slot E i): Tendsto (fun x:ℕ×ℕ=> T.onSlot i s x.1 x.2) τ (𝓝 (labelSlot E i s)):=by
   unfold onSlot labelSlot; by_cases h:s.1.val%2=0
   · simp_rw [if_pos h]; exact (T.tends _ _).star
   simp_rw [if_neg h];exact T.tends _ _
include hT
lemma tick_pass {S : Table C.book} (H : F.PointLimits C S) (e : b ≤ k) : ∀ᶠ t : ℕ in atTop,
    Tendsto (fun c : ℕ × ℕ => moment (C.beta c.1 c.2) (tick T i e t c.1 c.2)) τ
      (𝓝 (S.expect (E.flick e t m i))) := by
  filter_upwards [translate_generic E i e] with t ht
  rw [flick_realized E i e t, Table.readAt]
  let x a:= placeSlot E i e t ((slots E i).get a); let d a:=gradeSlot E i ((slots E i).get a)
  let v : C.book.Vector d:=fun a=> labelSlot E i ((slots E i).get a); let z (u:ℕ×ℕ) a:= T.onSlot i ((slots E i).get a) u.1 u.2
  let Q (c:ℕ×ℕ):= C.ensemble d (fun a => location C.S k c.1 c.2 (x a)); let Y:= S.value d (Extraction.Order.grid C k x)
  have hL (w:C.book.Vector d) : Tendsto (fun u=> Q u w) τ (𝓝 (Y w)):=
     (Extraction.Order.along (eventual_grid C F S H x ht (fun i=> ⟨d i,w i⟩))).mono_left hT
  exact Next.UVStress.tendsto_multi _ Q (⇑Y) hL v z (fun a=> on_limits T i _)
lemma wanted {S : Table C.book} (H : Seed C F S) (e : b ≤ k) (m:ℕ) : ∀ᶠ t : ℕ in atTop,
    Tendsto (fun c : ℕ × ℕ => fromCut T e t m c.1 c.2) τ (𝓝 (E.wanted e t m S)):=by
  filter_upwards [eventually_all.mpr (fun i : Fin (2*m) → Fin E.num => tick_pass T i hT H.generic e)] with t ht
  unfold Episode.wanted
  apply Tendsto.congr' (((fromCut_expand T H.cutoff e m t).filter_mono hT).mono fun _ hc => hc.symm)
  exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul (ht i)
end
end Ticket
open OS OS.Ground Org Phase
open scoped NNReal InnerProductSpace
variable {S : Table C.book}
-- unify computations over the same worlds family
abbrev Viewer (V : Final C F S) := Option V.α.space.X
def watches (V : Final C F S) (u:Viewer V): Table C.book:= u.elim S V.α.ensemble
lemma watched_kernel (V : Final C F S) (u:Viewer V): (watches V u).Hierarchy:= by cases u ; exacts [V.room.kernel,V.phase.phase.states _]
lemma respects_kernel (V : Final C F S) (u:Viewer V): (watches V u).respects S:= by cases u; exact fun _=> le_rfl; exact fun d=> (V.phase.phase.retains _ d).symm.le
lemma watched_inclusions (V : Final C F S) (u:Viewer V): V.sector.derivatives.Inclusions (watches V u) := by cases u ; exacts [V.phase.transport.injection,V.phase.phase.coordinates _]
lemma watched_derivatives (V : Final C F S) (u:Viewer V): V.sector.derivatives.Derivatives (watches V u) := by cases u ; exacts [V.phase.transport.derivatives,V.phase.phase.calculus _]
lemma watched_turns (V : Final C F S) (u:Viewer V): V.sector.turns.Oriented (watches V u) := by cases u ; exacts [V.phase.transport.motion,V.phase.phase.sym _]
namespace Ticket
variable {E τ}[τ.NeBot](T:Ticket E τ)(hT:τ≤F.fuse)(V : Final C F S) (hp:Grill C F)
   (g:ℝ) (ht:0≤g) (e:b≤k)
   (hE:∀ m, ∀ᶠ t in atTop, ∀ᶠ c:ℕ×ℕ in τ, ‖T.fromCut e t m c.1 c.2‖ ≤ g^(2*m))
include T hT hp ht e hE
lemma watches_le (u : Viewer V) : ‖∑ i,E.factor i*(watches V u).expect (E.word i)‖ ≤ g:=by
   let A:= V.α.unselected; let K:= V.room.kernel; let Z:= V.phase.phase; let R:= V.α.space; have hs: Steady V.α.room:= Z.still
   have hy:= Work.B03.answer K V.sector.derivatives V.α.room A hs Z.lengths; have hx:= Work.B05.answer Work.B04.answer V.room hp V.sector V.phase.transport V.α.room A hs hy
   have hv : Retain.Tall A (E.cluster A) g := by
      intro n
      apply le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp (Work.B17.answer V.room V.α.room A hy hs hx b k e E n))
      filter_upwards [wanted T hT V.room e n,hE n] with t h1 h2
      apply le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp h1)
      apply h2.mono; intro i H; exact (Complex.re_le_norm _).trans H
   have hd i: distinct (E.word i):= (realized ..).2 (generic_conf _ (E.gen i))
   have H i : ∑ a,E.factor a * (V.α.ensemble i).expect (E.word a) = R.character i (E.cluster A):= by
      unfold Episode.cluster
      rw [map_sum]; apply Finset.sum_congr rfl; intro j _
      rw [Retain.picky A R, Retain.pops A R (Z.chosen i)]
   have hR i: ‖∑ a,E.factor a * (V.α.ensemble i).expect (E.word a)‖ ≤ g := by rw [H]; exact Retain.bit A Z.decomposition _ _ ht hv _
   cases u with
   | some u=>exact hR _
   | none =>
     change ‖∑ i,E.factor i*S.expect (E.word i)‖ ≤ g
     have hZ:= Z.decomposition.normalized
     let w (j:Fin E.num)(x:R.X):= (V.α.ensemble x).expect (E.word j)
     have hx j : ∫ x, w j x ∂R.μ = S.expect (E.word j) := R.barycenter _ Z.decomposition Z.chosen K.translations _ (hd j)
     have hw j : Continuous (w j):= by
        unfold w; simp_rw [← (fun x=> Retain.pops A R (Z.chosen x) _ (hd j))]; exact Z.decomposition.weak _
     let f (x:R.X):=∑ j,E.factor j*w j x
     have hz : ∫ x,f x ∂R.μ=∑ j, E.factor j*S.expect (E.word j):=by unfold f; rw [integral_finsetSum _ (fun j _=> ((hw j).integrable_of_hasCompactSupport (μ:=R.μ) (HasCompactSupport.of_compactSpace _)).const_mul (E.factor j))]; simp_rw [integral_const_mul,hx]
     rw [← hz]
     calc ‖_‖ ≤ ∫ _x:R.X,g ∂R.μ:= norm_integral_le_of_norm_le (integrable_const _) (Eventually.of_forall hR)
          _ = _ := by simp
end Ticket
end YM.Contacts.Costar
