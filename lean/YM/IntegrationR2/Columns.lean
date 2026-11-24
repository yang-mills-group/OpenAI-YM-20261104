import YM.IntegrationR2.Socket
import YM.IntegrationR2.Evaluation

/-!
# Column-side producer. See ReservePlate and Vertex-facing run endpoint

Even off the graph, price repeated/historical uses of forces in the *actual*
canonical represented alphabet. At a local step apply to the whole column and
to actual differences (Lipschitz prices). Includes exact density semantics;
don't infer these merely from estimates or vice versa. Last lemma here issues
the +2 regular reserve for all actual `Matric.Gram` reads (not the reflected
two-point Gram IR matrix!). Proof of amplification adapted from `Tool.stained`
and `Gram.prose`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric.R2
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{H:History G} {N p m:ℕ} {Y:Hol G}
set_option quotPrecheck false
local notation "A₀"=>H.rep N p m
local notation "A₁"=>H.rep N p (m+1)
local notation "Z"=> orbitCost F
local notation "μ"=>kappa H m
local notation "μ'"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "s"=> (H.levels.params (m+1)).columns
local notation "s'"=> (H.levels.params m).columns
variable {S:Desk G (H.S.side (m+1) p)}{E:Desk G (H.S.side m p)}
variable (P:Tool F H N p m){D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{W:Worth}{T:Heading F}{c ε v t:ℝ}{X:Set Wing}
variable (hx:P.Cap B Y W D T c ε v X)(h:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
variable (Hplus:ReservePlate B H N p m Y (H.rep N p (m+1)) (H.S.block m) P.plate c ε D)
    (i:F.Index)(f g: Coin F Y S)
local notation "J"=> Size.axis F i
include hx h

omit Hplus in
lemma breakOrder :
    (breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g))).density 0 B A₀ = blast H N p m d ((book (0:F.Coeff) (Coin.uses (f-g))).density 0 B A₁) := by
  let F':=book J (Coin.uses f); let G':=book J (Coin.uses g)
  obtain ⟨he,hf⟩:=granted h Y J f; obtain ⟨hu,hg⟩:=granted h Y J g
  have hp:= (P.recoil hx h i f).earns; have hz:= (P.recoil hx h i g).earns
  rw [eval_sub (P:=P.shot i (Coin.uses f)) (Q:=P.shot i (Coin.uses g)) B rfl (hx.shines.represents N p m hx.late.le).good hp.bound hz.bound, hp.agrees,hz.agrees, ← blast_diff _ _ _ _ _ _ _ (play_integrable _ _ hx.shines hx.late he hf) (play_integrable _ _ hx.shines hx.late hu hg)]
  rw [←eval_sub (P:=book J (Coin.uses f)) (Q:=book J (Coin.uses g)) B rfl (hx.shines.represents N p (m+1) hx.late).good hf hg]
  congr 2
  rw [map_sub,show breakP (book J (Coin.uses f)) (book J (Coin.uses g))=book (J-J) (Coin.uses f-Coin.uses g) from rfl,sub_self]

include Hplus
lemma recoilPlus (a b:ℝ) (hp:Tab (book J (Coin.uses f)) 0 A₁ μ' a b) :
    let x:=J; let A:=book J (Coin.uses f)
    let w:=a+μ'*b
    Span B H N p m Y (P.shot i (Coin.uses f)) (A.exponentialEntry 0 B A₁) (profile (A₁).activities A.forced) (x 0) D X (A.density 0 B A₁) (T.leads (H.S.block m) x)
       (ε*(F.coeffSize (F.core x)+w)) (c*F.coeffSize (vowel F (H.S.block m) (F.core x))+ε*w) (v+2*w) ∧
    Plus A₀ (P.shot i (Coin.uses f)) (c*F.coeffSize (vowel F (H.S.block m) (F.core x))+ε*w) :=
    splitDesign B H N p m Y P.plate P.up (book J (Coin.uses f)) X D i hx.shines hx.late (granted h Y J f).1 hp rfl rfl hx.dish hx.budget.epsilon hx.copies Hplus hx.cart

omit Hplus hx in
lemma coinTab (j:F.Index)(f:Coin F Y S) (hg:(Coin.uses f).1 = 0) :
    Tab (book (Size.axis F j) (Coin.uses f)) 0 A₁ μ' 0 ‖f‖ := by
  obtain ⟨a,b,hv,hQ⟩:= rem_tabs.mp (granted h Y (Size.axis F j) f).2
  refine ⟨hv.divisor,le_rfl,norm_nonneg _,?_,?_⟩
  · rw [bookE,hg]; exact ⟨fun _=>0,budget0 ..,fun _=> (regular0 ..).2⟩
  obtain ⟨u,ha,hb⟩:=hv.forced
  have he:b≤‖f‖:= (le_add_of_nonneg_left hv.first).trans hQ
  exact ⟨u,Local.sumBudget_mono ha ha.1 (fun _=>le_rfl) (mul_le_mul_of_nonneg_left he hv.divisor.le),hb⟩

/-- A real flat gate (plus density equality) filling the Lipschitz supplier for
one historical graph direction: if files differ in just the forced component,
we get µ' extra. Use `socketPlus` to supply the regular bill for mixed pairs. -/
lemma forcedDirection (ha:Afford P.plate Y (H.rep N p (m+1)) (H.rep N p m))
    (hE:(Coin.uses f).1=(Coin.uses g).1) :
    let A:= breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g))
    A.density 0 B A₀=blast H N p m d ((book (0:F.Coeff) (Coin.uses (f-g))).density 0 B A₁) ∧
    Gate A A₀ Y μ (ε*(μ' * ‖f-g‖)) ∧ Plus A₀ A (ε*(μ' * ‖f-g‖)) := by
   have hP:= coinTab h i (f-g) (by rw [map_sub,Prod.fst_sub,hE,sub_self])
   have hv:= socketPlus P hx h i f g Hplus ha hP
   rw [zero_add] at hv
   exact ⟨breakOrder P hx h i f g, hv⟩
variable (Q : Gram F Y S ((H.levels.params (m+1)).columns))
variable (hp:roomCost H.levels W)(hk:Bank W H.levels)
local notation "ξ" => (fun x:F.Coeff=>F.coeffSize (vowel F (H.S.block m) (F.core x)))
local notation "ρ" => c+ε*s
include hp hk
lemma columnsBudget (x:F.Coeff): Blown (Q.point P x) 0 A₀ (s'*F.coeffSize (F.core (Q.point P x).x)):=by
  have he : 0 ≤ ε:=hx.budget.epsilon; have h' : 0 ≤ s:=zero_le_one.trans (H.levels.params (m+1)).columns_ge
  have hQ(i:Tally F): Blown (P.portfolio Q.scythe i) 0 A₀ ((ρ)* (ξ) (Size.axis F i.2)) := by
     let x:=Size.axis F i.2; let f:=Q.scythe i.2; have ht:= (P.recoil hx h i.2 (Q.scythe i.2)).earns
     obtain ⟨a,b,Hb,hv⟩:= rem_tabs.mp (granted h Y x f).2
     have hs:= (recoilPlus P hx h Hplus i.2 f a b Hb).2
     have hF: a+ μ' * b ≤ s * ξ x:=
        (calc _ ≤ a + b := add_le_add_right (mul_le_of_le_one_left Hb.second hx.hv) a
              _ ≤ s * F.coeffSize (F.core x):= hv.trans (Q.toll x)
              _ ≤ _ := mul_le_mul_of_nonneg_left (Work.G08.size_vowel F _ _).1 h')
     refine Blown.enlarge (hs.orientPaid i.1 (P.whirl i.1) ht.format ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S m p))) ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hF he)).trans (le_of_eq ?_))
     unfold x; ring
  have hc:0 ≤ c+ε*s:=add_nonneg (zero_le_one.trans hx.budget.cost) (mul_nonneg he h')
  obtain ⟨-,hY,hx⟩:= P.stained hx h Q.scythe (fun i=> Q.toll _) x
  have hz:= Blown.pencil_joins (code (Tally F)) hQ (chips F) x
  exact hz.enlarge ((residual_bill F (H.S.block m) (c+ε*s) hc x).trans (Work.G08.cone_step W H hp hk m F _ _ _ _ hx le_rfl).1)
end YM.MergeProof.Matric.R2
