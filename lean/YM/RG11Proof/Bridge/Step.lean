import YM.RG11Proof.Bridge.Residual
/-!
# Absorb on one joint detector transition

Only assumes radius-independent regulator removal rates through the given n,
approximate re-expression in residual form and leading detector hypotheses (OR
Detector of finite precision with explicit Restore). The main theorem `current`
doesn't assume coefficients of the common-regulator matching frame are bounded or
remain small in all orders. It proves regulator convergence with the stated rate
at order n and continuum transformed correlation identity there (and glueing in
a subsequent file). Supply the physical/top-regulator inputs first; using this at
a coupling-domain test against actual correlations is NOT justified.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bridge
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Formal YM.RG11.Rate Filter
open scoped BigOperators Classical
variable {J P α : Type*} [Fintype J] [DecidableEq J] {shape:P→ℕ}
variable {k : Budget α} {L : Constraints ℝ J} {A B : ArrayAt J ℝ shape}
variable {V D : α→ArrayAt J ℝ shape} {T : α →Change ℝ J} {M n : ℕ} {m : Finset (Mark J shape)}
local notation "PS"=>PowerSeries ℝ

def Crest (k : Budget α) (n : ℕ) (D : α→ArrayAt J ℝ shape) (B : ArrayAt J ℝ shape) (v : Mark J shape) :=
  Pieces k n (fun a=>D a v) (fun _=>B v)

/-- Candidate outputs through power n as independently solved by the finite
detector on A,B (non-constructor here). Transform laws & hits available.
Assumes that the overlap m has the indicated up-to-D-and-n rate including
all field choices needed AFTER conversion, not merely those already in m.
No agreement on position domains outside m follows from this input. -/
theorem carried {v : Mark J shape} (hv : v∈m) (hn : 0<n) (hm : n≤M)
    (T0 : ∀ a, Anchored (T a).g)
    (e : Saves k M m V D T)
    (hV : ∀ w,Crest k n V A (⟨v.1,w⟩:Mark J shape)) (hD : Crest k n D B v)
    {p : Change ℝ J} (hp : Law L p) (x : α→Step L) (h : Older n k T p) (hc : Current L k T n x) :
    Carry k (fun a=>coins (x a)) (fun _=> coeff n (B v))
       (fun a => coeff n (p.act A v) + fullRead L A (x a-seen p hp n hn) v) := by
  let q := fun a=> replace p n (x a)
  have hQ a : Law L (q a):= lawful_replace hp (x a) hn
  have hw := olderUnpaid x p h hc
  have ha:= OnChange.response hw T0 (fun a=> (hQ a).1) hn (A:=V) (B:=fun _=>A) v hV
  let W := fun a=>coins (x a)
  have hb := (NearFn.symm (show NearFn k _ _ from (hD.price (le_refl n)))).carry W -- le rfl
  have H := Carry.trans hb (Carry.trans (e.unpaid hn hm hw hv) ha.top)
  -- Replace transformed coefficients using the exact n-pencil.
  have he a : coeff n (p.act A v) + fullRead L A (x a-seen p hp n hn) v=coeff n ((q a).act A v) := by
    let u := x a - seen p hp n hn
    have h0 : Strike n p.g (q a).g u.2 := by
      constructor
      · intro i hi; rw [show coeff i (q a).g = _ from addressed ..,if_neg hi.ne]
      change coeff n p.g + ((x a).2 - _) = _; rw [show coeff n (q a).g = _ from addressed ..,if_pos rfl]; change coeff n p.g + (_-coeff n p.g)=_; abel
    have h1(i j) : Strike n (p.Z i j) ((q a).Z i j) (u.1.val i j) := by
      have h2 (w) : coeff w ((q a).Z i j) = (if w=n then (x a).1.val else piece w p.Z) i j:= by
        rw [← piece_apply, show q a=_ from rfl]; change piece w (replace p n (x a)).Z i j=_; rw [positioned]
      constructor
      · intro r hr; rw [h2,if_neg hr.ne,piece_apply]
      rw [h2,if_pos rfl]; change coeff n (p.Z i j) + (_ - piece n p.Z i j) = _; rw [piece_apply]; abel
    exact (pencil_action hn hp.1 hp.2.baseline h0 h1 v).value
  exact Carry.congr H (EventuallyEq.refl ..) (Eventually.of_forall (fun a=> (he a).symm))

-- Needed uniform for at least the detector's profile test coordinates.
def TestDemand (Q : Detector L A) : Finset (Mark J shape) := Finset.univ.image Q.test

theorem current (Q : Detector L A) (x : α→Step L) (hn : 0<n) (hm : n≤M) (hc : Current L k T n x)
    (T0 : ∀ a, Anchored (T a).g) (e : Saves k M m V D T) (hs : TestDemand Q ⊆ m)
    (hV : ∀ v∈m,∀ w,Crest k n V A ⟨v.1,w⟩)
    (hD : ∀ v∈m,Crest k n D B v)
    (h : Older n k T (solution Q B)) :
    (∀ i : Asking J, Near k (fun a=> readOne L i (x a))
                      (readOne L i (seen (solution Q B) (solution_law Q B) n hn))) ∧
    Bounded k (fun a=> coins (x a)) := by
  let W := fun a=>coins (x a)
  let Y := seen (solution Q B) (solution_law Q B) n hn
  have he (t : Fin Q.m) :=
    carried (k:=k) (hv:=hs (Finset.mem_image_of_mem _ (Finset.mem_univ t))) hn hm T0 e
        (v:=Q.test t) (hV (Q.test t) (hs (Finset.mem_image_of_mem _ (Finset.mem_univ t))))
        (hD _ (hs (Finset.mem_image_of_mem _ (Finset.mem_univ t)))) (solution_law Q B) x h hc
  have hz (i: Asking J): Carry k W (fun a=>readOne L i (x a)) (fun _=>readOne L i Y):= by
    let Λ:= readOne L i
    let L' := Λ.comp Q.restore
    have hh:= (carry_linear L' he).symm
    have hv(a): L' (fun t=> coeff n ((solution Q B).act A (Q.test t))+ fullRead L A (x a-Y) (Q.test t))
        = Λ (price Q ((solution Q B).act A) n)+ (Λ (x a)-Λ Y):= by
      rw [show (fun t => _ + fullRead L A _ (Q.test t))=
          (fun t=> coeff n ((solution Q B).act A (Q.test t))) + (fun t=>fullRead L A (x a-Y) (Q.test t)) from rfl,map_add]
      dsimp [L']; rw [Q.works,map_sub]; rfl
    change Carry k W (fun a=> L' (fun t=> coeff n ((solution Q B).act A (Q.test t))+fullRead L A (x a-Y) (Q.test t)))
           (fun _=> Λ (price Q B n)) at hh
    have ht : price Q B n = _ := hits Q B hn
    simp_rw [hv,ht] at hh
    unfold Carry at hh ⊢; simpa only [add_sub_cancel_left] using hh
  have hw := absorb (y:=fun a i=>readOne L i (x a)) (u:=fun i=>readOne L i Y) hz
  exact ⟨hw.2,hw.1⟩

theorem newer (Q : Detector L A) (x : α→Step L) (hn : 0<n) (hm : n≤M) (hc : Current L k T n x)
    (T0 : ∀ a, Anchored (T a).g) (e : Saves k M m V D T) (hs : TestDemand Q ⊆ m)
    (hV : ∀ v∈m,∀ w,Crest k n V A ⟨v.1,w⟩)
    (hD : ∀ v∈m,Crest k n D B v)
    (h : Older n k T (solution Q B)) :
    Older (n+1) k T (solution Q B) := by
  obtain ⟨hi,hb⟩ := current Q x hn hm hc T0 e hs hV hD h
  constructor
  · intro i hh; obtain rfl|hh:=eq_or_lt_of_le (Nat.le_of_lt_succ hh); swap; exact h.1 _ hh
    exact (hc.1.boundedWeight hb).turnsNear (hi none)
  intro i hh; obtain rfl|hh:=eq_or_lt_of_le (Nat.le_of_lt_succ hh); swap; exact h.2 _ hh
  exact fun j l=> (Carry.boundedWeight (hc.2 j l) hb).turnsNear (hi (some (j,l)))
end YM.RG11.Bridge
