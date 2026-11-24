import YM.RG01Estimate.Caddies
/-!
 # Main shelf's purchases from a priced enumeration; propagate exact common masks.
   P accrual + U payment + V overholding. Separate lack slots for
   leftovers from opening & pruning on both ask and pay. Requires mirrored
   labels on all regular families and complaints. No comparison to other basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Caddy
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Meadow Marlin Trio
open Geo Footprint Animals Abacus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c:Side}(p:BudgetPoint)(A:Listing G c) (M: Listing G c)
  (F:Collection.Source G c) (P L E : ℕ→ Config G c→ℝ)
variable {k f : ℕ→ ℝ}{b t q u v w η : ℝ} {r:ℕ}
     (hF: Collection.Local A p F t b)
     -- needs Hull for L and E. L genuine payment fragment. E candidate payment.
     (N:Rack A r L) (J:Rack M r E)

local notation "I" => (stores A M.reg)
local notation "F'" => posted F
local notation "P'" => righty P
local notation "X'" => (insertP (-E) L)
local notation "V'" => (insertP (-(P-E)) (F.logRead-L))

variable (hq: Meadow.Budget p A.reg (F.logRead-L) u)
     (hp : Meadow.Budget p M.reg P v)(hP: Meadow.Budget p M.reg E w) (hX:Meadow.Budget p M.reg (P-E) η)(hL: Meadow.Budget p A.reg L q)
     (hY: ∀ s b, Nonempty ((A.read (revise F (F.logRead-L))).Moves s b))
     -- source producer P drives these together. in real analyzer P' candidate from U.form.
     (hQ: ∀ s b, Nonempty (Mirrors M.reg s b P))(hE: ∀ s b, Nonempty (Mirrors M.reg s b (-(P-E))))
     (hZ : ∀ s b,Nonempty (Mirrors M.reg s b E))
lemma turns (X:ℕ→ Config G c→ℝ) (s : Signed) (b:Site c)(h: Mirrors M.reg s b X): Nonempty (Mirrors M.reg s b (fun _ : ℕ=> (0:Config G c→ℝ))) := ⟨⟨h.walks,h.hooks,h.hues,fun _=>rfl⟩⟩
-- Full roster and Masks. rev lemma supplies AUTH CADDIES formulas.
include hF hY hQ hE hZ
lemma symmetry : ((I).read (revise F' (P'+V'))).ForcedFamily p ∧
       ∀ s b, Nonempty (((I).read (revise F' (P'+V'))).Moves s b) ∧ Nonempty (((I).read F').Moves s b) ∧
             Nonempty (((I).read (revise F' P')).Moves s b) ∧ Nonempty (((I).read (revise F' V')).Moves s b):= by
    let X:= I; let V:= V'; have he:=hF.family
    refine ⟨⟨he.sym,he.symtest,he.meas,he.meas_test,he.reads,he.reads_test,he.permit⟩,fun s b=>?_⟩
    have hm:= Classical.choice (hF.transforms s b)
    let w := Classical.choice (hY s b); let Y:= revise F (F.logRead-L)
    let M':=M.reg; let e':= Classical.choice (hQ s b)
    have hv : Nonempty ((X.read (revise (posted Y) V)).Moves s b):= Moves A M' _ s b w (Classical.choice (hE s b))
    have hx : Nonempty ((X.read (posted F)).Moves s b):= Moves A M' F s b hm (show Mirrors M.reg s b 0 from (turns M P s b e').some)
    refine ⟨?_,hx,?_,hv⟩
    · have he: P'+V'= insertP E (F.logRead-L):= by
         funext i; change Sum.elim (fun _=>0) P (e i)+ Sum.elim (F.logRead-L) (-(P-E)) (e i)=_; change _= Sum.elim (F.logRead-L) E (e i); rcases e i with i|i
         · simp
         simp
      rw [he]; exact Moves A M' Y s b w (Classical.choice (hZ s b))
    have hh:Nonempty ((A.read (revise F 0)).Moves s b):= nil_move A F s b hm _ fun _=>rfl
    exact Moves A M' (revise F 0) s b hh.some e'

omit hF hY hQ hE hZ
include hp hP hX hq hL
lemma shelf : (F').logRead=P'+V'+X' ∧ Meadow.Budget p (I).reg (P':ℕ→ Config G c→ℝ) v ∧ Meadow.Budget p (I).reg V' (u+η) ∧ Meadow.Budget p (I).reg X' (q+w) := by
    have neg (f:ℕ→ Config G c→ℝ) (g:ℝ) (h:Meadow.Budget p M.reg f g): Meadow.Budget p M.reg (-f) g:= by simpa only [zero_sub,zero_add] using pay_gap p (pay_zero (G:=G) p M.reg) h
    refine ⟨?_,?_,posting_bounds p A M.reg hq (neg _ _ hX),posting_bounds p A M.reg hL (neg _ _ hP)⟩
    · funext i; change Sum.elim F.logRead (0:ℕ → Config G c→ ℝ) (e i) = (Sum.elim (fun _:ℕ=>0) P (e i) + Sum.elim (F.logRead-L) (-(P-E)) (e i)) + Sum.elim L (-E) (e i); rcases e i with i|i <;> simp -- Abel
    simpa only [zero_add,righty] using posting_bounds p A M.reg (pay_zero (G:=G) p _) hp
-- all path preservation of Ip entries
omit hp hP hX hq hL
lemma returns (i:ℕ): (((stores A M.reg)).reg (Caddy.e.symm (.inr i)))=M.reg i ∧
    (Caddy.righty P (Caddy.e.symm (.inr i))) = P i:= by
   simp only [stores,Function.comp_apply,Caddy.e.apply_symm_apply,Sum.elim,Caddy.righty,Caddy.insertP,and_self]

end YM.RG01Estimate.Caddy
