import YM.Next.MAXWELL.Double
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Canopy
import YM.Next.RANK.GaussLeg
import YM.Next.RANK.GaussTags

/-!
# To separate color slots in stabilizer proof

Use a *redundant* presentation of Wick words. Very convenient for transmission of arbitrary
polarizations. It's important that later derivatives which are demanded by our span argument
respect the one-slot linear relations. Work with one algebra even when adding a fresh probe
at some clear position. Polynomials have only finite supports!
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Function Set Finsupp Maxwell Maxwell.Free Maxwell.Wick
open MvPolynomial Next.Rank.Normal
open scoped BigOperators Classical

abbrev Key := Σ j, Flavor j
abbrev Paint (G : Gauge):= Key × G.ColorIndex
abbrev World (G : Gauge):= E4 × Paint G
abbrev Pol (G : Gauge):= poly (World G)
variable {G : Gauge} {n : ℕ}
def qr (p : Paint G) := flavor (G:=G) p.1.1 p.2 p.1.2

def action (p : Paint G) : Slot G →₀ ℂ := ∑ i, (qr p (frame G p.1.1 i):ℂ) • single (α:=Slot G) ⟨p.1.1,i⟩ 1

def send := (exchange (action (G:=G)) : poly (Paint G) →ₐ[ℂ] WickPol G)
lemma sends (i : Paint G) : send (X i)=bit i.1.2 i.2:=by unfold send; simp only [exchange_x,glyph,action,map_sum,map_smul,linearCombination_single,one_smul, ← MvPolynomial.C_mul']; rfl
def enroll : WickPol G →ₐ[ℂ] poly (Paint G):= aeval (R:=ℂ) fun i : Slot G=> ∑ c:G.ColorIndex,X ((⟨i.1, flavor_pick (coordinateLeg i) c⟩,c) : Paint G)
@[simp] lemma recovers (p : WickPol G) : send (enroll p)=p:=by
  suffices h : send.comp (enroll (G:=G))=AlgHom.id ℂ _ from DFunLike.congr_fun h p
  ext1 i; rw [AlgHom.comp_apply,enroll,aeval_X,map_sum]; simp_rw [sends]; exact (divide (coordinateLeg i)).symm.trans (symbol_coordinate i)

lemma convey (A : TaylorTower G) (p : poly (Paint G)) : probe A (send p)=aeval (fun i => ((available (A i.1.1) i.1.2 i.2:ℝ):ℂ)) p:=by
  suffices h : (probe A).comp send= aeval (fun i : Paint G => ((available (A i.1.1) i.1.2 i.2:ℝ):ℂ)) from DFunLike.congr_fun h p
  ext1 i; rw [AlgHom.comp_apply,sends,bit,symbol_test,aeval_X]; rfl

def Kf (G : Gauge): Symmetric (World G) where
  cov u v:= linkEntry (u.1,⟨_,qr u.2⟩) (v.1,⟨_,qr v.2⟩)
  symm u v:=by
    unfold linkEntry; dsimp only
    by_cases h:u.1=v.1; simp [h]
    rw [if_neg h,if_neg (Ne.symm h),K_symmetric _ _ h]
lemma empty_self (x : E4) (i j : Paint G) : (Kf G).cov (x,i) (x,j)=0:= if_pos rfl
-- order of flavor (orientation of curl derivatives) matters!
lemma cash (u v : World G) (h : u.1≠v.1): (Kf G).cov u v = (legKernel (qr u.2) (qr v.2) (u.1-v.1): ℝ):= if_neg h
lemma colors (c : G.ColorIndex) {x y : E4} (h : x≠y) (i j:Key) (a b : G.ColorIndex):
    (Kf G).cov (x,i,a) (y,j,b)= if a=b then (fare c i.2 j.2 (x-y):ℂ) else 0:= by
  rw [cash _ _ h]; change ((legKernel (flavor i.1 a i.2) (flavor j.1 b j.2) (x-y):ℝ):ℂ)=_
  rw [any_ink c i.2 j.2 a b (sub_ne_zero.mpr h)]; split_ifs <;> simp

def receive (G : Gauge): Pol G →ₗ[ℂ] ℂ:= Next.Rank.Normal.blend (Kf G) 0

def plays (x : Points n) (z : Fin n × Paint G): World G := (x z.1, z.2)

def product (x : Points n) (a : Fin n → poly (Paint G)): Pol G:=∏ i, post (x i) (a i)
lemma play_product (x : Points n) (a : Fin n → poly (Paint G)): product x a=(rename (plays x)) (pot Finset.univ a):= by
  rw [product,pot,map_prod]; refine Finset.prod_congr rfl fun i _=>?_; rw [post,post,rename_rename]; rfl
lemma product_cons (x : Points n) (z : E4) (a : Fin n → poly (Paint G)) (p : poly (Paint G)) : product (Points.cons z x) (Fin.cons p a)=post z p * product x a := by rw [product,Fin.prod_univ_succ]; rfl

private lemma bilinear (i j : Fin n) (Q : Symmetric (Fin n × Slot G)) (a b : Slot G →₀ ℂ):
    treats Q (mapDomain (fun x => (i,x)) a) (mapDomain (fun x => (j,x)) b) =
    linearCombination ℂ (fun x => linearCombination ℂ (fun y => Q.cov (i,y) (j,x)) a) b:=by
  unfold treats; rw [linearCombination_mapDomain,linearCombination_mapDomain]
  apply congr_arg (fun n => linearCombination ℂ n b); funext y; simp only [Function.comp_apply,linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply]
private lemma counts (x : Points n) (hx : x ∈ conf n) : scope (perSlot (fun _ : Fin n=> action (G:=G))) (frameX hx)=scope (fun i=> single (plays x i) 1) (Kf G):=by
  have he (a:Paint G): qr a=∑ i, qr a (frame G _ i) • coordinateLeg (⟨a.1.1,i⟩ : Slot G):=by
    ext1 v; conv_lhs=>rw [← (frame G _).sum_repr v]
    rw [map_sum,LinearMap.sum_apply (M:=Shell G a.1.1) (σ₁₂:=RingHom.id ℝ)]; simp_rw [map_smul]; exact Finset.sum_congr rfl fun _ _ => mul_comm ..
  apply Symmetric.ext; funext ⟨i,a⟩ ⟨j,b⟩; rw [match_name (plays (G:=G) x)]; change treats _ (mapDomain _ _) (mapDomain _ _)=(Kf G).cov (x i,a) (x j,b); rw [bilinear i j]
  by_cases h:i=j; subst i; simp [frameX,linearCombination_apply,empty_self]
  let s:= x i-x j; have hs: x i≠x j:= (show Injective x.ofLp from hx).ne h
  let J := Maxwell.pairing (show s∈away from sub_ne_zero.mpr hs) (G:=G) (j:=a.1.1) (l:=b.1.1)
  rw [cash _ _ hs]; change _=(J (qr a) (qr b):ℂ)
  conv_rhs=> rw [he a,he b,map_sum J]; simp only [LinearMap.sum_apply,map_smul]
  simp only [action,map_sum,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro z _; simp only [linearCombination_single,one_smul]; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _; unfold frameX; dsimp only; rw [if_neg h]; rfl
private lemma dry_reads {σ τ : Type*} (m : σ → τ →₀ ℂ) : reads m 0=0:= funext fun _=> linearCombination_zero_apply ..
lemma delivered (x : Points n) (hx : x ∈ conf n) (a : Fin n → poly (Paint G)):
    receive G (product x a)=moment G x (fun i=> send (a i)):=by
  rw [play_product, Wick_reads hx]; unfold send; let z:= action (G:=G); let t : Fin n×Paint G → (Fin n × Maxwell.Slot G)→₀ℂ:= perSlot (fun _ : Fin n=> z)
  change Next.Rank.Normal.blend (Kf G) 0 _ = Next.Rank.Normal.blend _ _ (∏ i, post i (exchange z (a i)))
  have hi : (∏ i: Fin n, post i (exchange z (a i)))= (Next.Rank.Normal.exchange t) (Next.Rank.Normal.pot Finset.univ a) := Eq.symm (by
    rw [pot,map_prod]; exact Finset.prod_congr rfl fun i _=> posts (fun _ : Fin n=>z) i (a i))
  rw [hi, labelled, wets, wets, dry_reads, dry_reads]; rw [show scope t (frameX hx)= scope (fun i=> single (plays x i) 1) (Kf G) from counts x hx]
end YM.XSpace.Legs
