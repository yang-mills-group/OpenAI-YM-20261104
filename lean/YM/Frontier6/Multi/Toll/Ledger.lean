import YM.Frontier6.Multi.Toll.Window

/-! Copy/separation-power economy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Lattice RG Wilson MergeProof Ribbons Canopies Finset Accent Fareway Extra.Histories Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open scoped Topology BigOperators Classical
variable {G:Gauge}{O:Type}[Fintype O][DecidableEq O]
variable (C:Family G)(hG:G.Simple)(t:O→ℕ)(d:ℕ)
variable {I:Type*}(T:Fareway I){r:ℕ→ℕ}{D:∀ N p i,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable {W:Worth}{u₁ ψ:ℕ→ℝ}(hW:Scrim C W u₁ ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D)
set_option quotPrecheck false
local notation "Q"=> C.path.levels
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "V"=> fly C.path.levels d
local notation "X"=> bling C.path.levels
local notation "n"=> Fintype.card O
variable (b:O→ℝ)(hb:∀ j,0<b j)

def σ (t:O→ℕ):ℕ:= ∑ i:O,t i
def forestPower (t:O→ℕ)(a c ε:ℝ) :ℝ:= (σ t:ℝ)*c+4*(↑(n):ℝ)*(c-a)+ ε*((n)*((n)+1):ℕ)
def welcome (t:O→ℕ) (w:ℕ)(a c b ε:ℝ) := ((w:ℝ)+1/16)*(a-b) - forestPower t a c ε
-- all prices at chosen size w-refinement

def rootRate (j:ℕ)(i:O):ℝ:= δ j*(η j*plumR C (t i) (b i) j)/8
def charge (j m:ℕ)(ε:ℝ):ℝ:= warrant C.S ε ((n)+1) (n) j (m+1) (total (rootRate C t b j))
def needQuota (d m:ℕ)(w:ℝ):ℝ :=4*(1+(Q|>.params m).columns)*(2*(C.S.a (m+1)^d*(X m*(1/(2*w)))))

include hG
lemma accounts : Note C.S (fly C.path.levels d) 0:= by
   unfold fly fog; simp_rw [← one_div]; exact (((Note.notes C.S _ one_pos).splits ((hut C hG).powerN _)).swapP (by simp))
include hb
lemma afford_rate (i:O): Note C.S (fun j=>rootRate C t b j i) (-(t i:ℝ)):=by
   obtain ⟨h,h'⟩:= mintN C hG
   exact ((h.mills (h'.mills (plumN C _ hG _ (hb i)))).splits (Note.notes C.S 8 (by norm_num))).swapP (by ring)

section
variable {T}{j k m:I→ℕ}{a c z ε:ℝ}(hj:Bench C.S T j c)(hm:Bench C.S T m a) (hk:Bench C.S T k z)
local notation "F"=>forestPower t a c ε
local notation "e!"=>fun i=> Real.exp (T.scale i*(-ε))
local notation "p!"=>fun i=> charge C t b (j i) (m i) (e! i)
local notation "q!"=>fun i=> needQuota C d (m i) (p! i)
local notation "hc"=>welcome t d a c z ε
include hm hj
lemma priceW : T.Mint p! (-F):=by
   let w(i):= total (rootRate C t b (j i)); let ε'(i):= e! i; let N':= Fintype.card O
   have ht := Mint.mass (T:=T) univ (fun x:O=>fun i=>rootRate C t b (j i) x) (fun x=> -(t x:ℝ)*c) (fun i _=> hj.notes (afford_rate C hG t b hb i))
   have he:(∑ i:O,-(t i:ℝ)*c)= -(σ t:ℝ)*c:= by unfold σ; rw [←sum_mul,Nat.cast_sum,← sum_neg_distrib]
   rw [he] at ht; have hh := hj.spacing.div (hm.succ C.path.levels.fits.mesh).spacing; let t0:= 4*N'; have hg:=T.minted (-ε)
   exact ((hh.power t0).mul ((hg.power (N'*(N'+1))).mul ht)).eq (by unfold t0 forestPower N'; push_cast; ring)
lemma budget_est : T.Mint q! (F-(d:ℝ)*a):=by
   let m' (i):=m i+1; have hv:= priceW C hG t b hb hj hm (ε:=ε); have ha:= (hm.succ C.path.levels.fits.mesh).spacing.power d; have ht:= hm.notes (banket C hG); have hs:= ((T.minted_c _ one_pos).common (hm.notes (fuNote C)|>.eq (by ring)))
   let o:=2*(σ t); have he:= (T.minted_c _ one_pos).div ((T.minted_c _ two_pos).mul hv);
   exact (((T.minted_c 4 (by norm_num)).mul hs).mul ((T.minted_c _ two_pos).mul (ha.mul (ht.mul he)))).eq (by ring)

local notation "s!"=>fun i=> Real.exp (T.scale i*hc)
lemma toll_paid (he:0<ε)(hy:z<a)(hk:Bench C.S T k z)(hp:Scrim C W u₁ ψ η δ (fly C.path.levels) r D) :∀ᶠ i in T.via,
   let x:=p! i
   0<x ∧ (march (fun _:Unit=>s! i) η (k i) (m i) () ≤ δ (m i)*(x/(16*X (m i)))) ∧
   32*(1+(C.path.levels.params (m i)).columns)* (s! i)*‖alto C.path (k i) d‖*(q! i/gainChart C.path (m i) (k i)) ≤ fly C.path.levels d (k i)/2:=by
   let S:=T.via; have hv:= priceW C hG t b hb hj hm (ε:=ε); have hz := budget_est C hG t d b hb hj hm (ε:=ε); let s i:= s! i; have hs:= T.minted hc; have ht:= hm.notes (banket C hG); have hF:= hm.notes (accounts C hG d); have hM:= hk.notes (accounts C hG d); let q i:= gainChart C.path (m i) (k i);
   have hq:T.Mint q ((1/8)*(a-z)):=by
      let g i:= Real.exp (((1:ℝ)/8)*C.S.scale i); have hg:=Note.bell_exp C.S ((1:ℝ)/8); refine ((hm.notes hg).div (hk.notes hg)|>.eq (by ring)).congr (Eventually.of_forall fun i=>?_); unfold q gainChart; rw [mul_sub,Real.exp_sub]
   have hL:= ((T.minted_c _ one_pos).common (hm.notes (fuNote C)|>.eq (by ring))); let p i:= s! i * (C.S.a (m i)/C.S.a (k i))^(d+1)*(fly (Q) d (m i)/fly (Q) d (k i))
   have heB:= ((hs.mul ((hm.spacing.div hk.spacing).power (d+1))).mul (hF.div hM)).cheaper ((hm.notes (mintN C hG).1).mul (hv.div ((T.minted_c 16 (by norm_num)).mul ht))) (by unfold welcome; push_cast; linarith)
   let u' i:= ‖alto C.path (k i) d‖
   have hQ:T.Mint u' (d*z):= by
       refine ((hk.spacing.power d|>.inv).eq (by ring)).congr (Eventually.of_forall fun i=>?_) ; unfold u'; rw [alto_norm]
   have hT := ((((T.minted_c 32 (by norm_num)).mul hL).mul hs).mul hQ |>.mul (hz.div hq)).cheaper (hM.div (T.minted_c _ zero_lt_two)) (by unfold welcome; linarith)
   filter_upwards [hv.pos,heB,hT,hk.later hm hy,hk.infinite.eventually_ge_atTop (C.ref d)] with i hi hp' hh hk hN
   exact ⟨hi,(seeing C d hp (Real.exp_pos _) (m i) (k i) hN hk.le).trans hp'.le, hh.le⟩
end
end YM.Frontier6.Road
