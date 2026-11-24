import YM.XSpace.Veneer
/-!
# Canonical and surveyed potentials paired into distinct marks
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Relief
open Function Set Filter Lattice Trace Chiral Litter Mu Tide Scale Pages Sail Chart2 Finsupp MvPolynomial Source
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge} {d e:ℕ} {H:Hol G}
def χ (c b:G.ColorIndex) : ℝ:= if b=c then 1 else 0
@[simp] lemma χ_self (c:G.ColorIndex): χ c c=1:=by simp [χ]
lemma κ (c b:G.ColorIndex): basisC G c b=χ c b:=by simp [EuclideanSpace.basisFun_apply,χ]
local notation "τQ" => Sail.cover
-- at V with potential edge

def steer (i j k:Axis) : Toe:= dotI j k • η i τQ-dotI i k • η j τQ
lemma health (i j k): steer i j k∈Terrain 3:= by unfold steer; refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (down_hill hill2 i)) (Submodule.smul_mem _ _ (down_hill hill2 j))
lemma payload (i j k:Axis)(v w:Cover)(c:G.ColorIndex): bake (Trace.touch w i j [] c) (v,k) = steer i j k (v-w) • basisC G c:=by
  have he (x:Cover)(p:Axis): bake (needle ((x,p),c)) (v,k)= (dotI p k*τQ (v-x)) • basisC G c:=by rw [baked]; unfold φ; rw [dot_at]; split <;> simp_all
  have hs (x:Cover) (p a:Axis): bake (gate [a] (needle ((x,p),c))) (v,k)=(dotI p k*(η a τQ (v-x))) • basisC G c:=by
    rw [gate,gate]; change bake (riff _ (needle _)) _=_; unfold riff; rw [LinearMap.sub_apply,pin, map_sub,Pi.sub_apply]; simp only [radius,LinearMap.id_apply,he]; rw [← sub_smul]; congr 1; change _= _ *(τQ (v-x-step a)-τQ (v-x)); rw [mul_sub, add_comm (step _), sub_add_eq_sub_sub]
  change bake (gate [i] _ - gate [j] _) _=_; rw [map_sub,Pi.sub_apply,hs,hs, steer, Pi.sub_apply,Pi.smul_apply,Pi.smul_apply,sub_smul];rfl

lemma ordered (j:Axis → Toe)(b:Bool)(p:P): -- moved derivative plaq sum identity on SC map for curl canonical
    (∑ u:PlaqAxes, q b p (six u) (endr u) • (D (six u) (j (endr u))-D (endr u) (j (six u))))=
       ∑ a:Axis,∑ i:Axis,q b p a i • D a (j i):=by
  let f(a i:Axis)(x:Cover): ℝ:= q b p a i * D a (j i) x; funext x; rw [Finset.sum_comm]; simp only [Finset.sum_apply]; change _=∑ i:Axis,∑ a:Axis,f a i x; rw [Feynman.order_cost (fun a i=> f a i x) (fun i=>by simp [f,qdiag])]; refine Finset.sum_congr rfl fun v _=>?_ ; let a:=six v; let i:=endr v; change q b p a i * (D a (j i) x-D i (j a) x) = f a i x+f i a x; unfold f; rw [chosen_sqrt2]; -- which
  ring
lemma roads (p:P)(b:Bool)(k:Axis): (∑ u:PlaqAxes,q b p (six u) (endr u) • steer (six u) (endr u) k)=∑ a:Axis,q b p a k • η a τQ:=by
  let h (a i:Axis)(x:Cover):ℝ:= q b p a i*dotI i k*η a τQ x; funext x; rw [Finset.sum_apply,Finset.sum_apply]; rw [show (∑ a:Axis, (q b p a k • η a τQ) x)= (∑ i:Axis,∑ a:Axis,h a i x) from ?_]; swap
  · rw [Finset.sum_eq_single (f:=fun i=>∑ a:Axis,h a i x) k]; apply Finset.sum_congr rfl; intro j _; simp [h,dot_at]; intro i _ hi; unfold h; simp [dot_at,hi]; simp
  rw [Feynman.order_cost (fun a i=> h a i x) (fun i=>by simp [h,qdiag])]; apply Finset.sum_congr rfl; intro u _; let a:=six u; let r:=endr u; change q b p a r • steer a r k x = _; rw [steer, Pi.sub_apply, Pi.smul_apply,Pi.smul_apply]; change _=h a r x+h r a x; unfold h; rw [chosen_sqrt2 b p a r]; simp only [smul_eq_mul]; ring

variable (g:G.Simple)(S:Survey G H d)(σ:Bool)(p:P)
abbrev field (σ:Bool)(p:P)(k:Axis): Toe:=∑ i:Axis, q σ p i k • η i τQ
abbrev uθ (s:RG.Slot)(k:Axis): Toe:=steer (six s.plaq) (endr s.plaq) k
def Mn (k:Axis): Toe:=∑ i:Fin S.size,coupon g S σ p i • mov (-(S.looks i).offset) (uθ (S.looks i) k)
lemma bunker (k:Axis): field σ p k∈Terrain 3:= by unfold field; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (down_hill hill2 i)
lemma shared (k:Axis):Mn g S σ p k∈ Terrain 3:=by unfold Mn; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (slide_hill (health _ _ k) _)
lemma stage (T:PlaqAxes→Toe)(he:2≤d): (∑ i:Fin S.size,coupon g S σ p i • T (S.looks i).plaq)=∑ u:PlaqAxes,q σ p (six u) (endr u) • T u:=by simp_rw [← remembrance g S σ p he,Finset.sum_smul,ite_smul,zero_smul]; rw [Finset.sum_comm]; simp
lemma stashed (he:2≤d)(k:Axis): Mn g S σ p k-field σ p k∈ Surface 3:=by
  unfold Mn field; rw [← roads p σ, ← stage g S σ p (fun i=>steer (six i) _ k) he,← Finset.sum_sub_distrib]; apply Submodule.sum_mem; intro i _; rw [← smul_sub]; exact Submodule.smul_mem _ _ (safekeeping (health _ _ k) _)
lemma beacon (p:Name G)(k:Axis)(x w:Cover): bake (cable g S σ p x) (w,k)= Mn g S σ p.1 k (w-x) • basisC G p.2:=by
  simp only [cable,slid_bake,zone_ap, wickLine,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,Mn,Finset.sum_smul,payload]; apply Finset.sum_congr rfl; intro i _; rw [smul_smul]; let a:=(S.looks i).offset; let T:=uθ (S.looks i) k; change (coupon g S σ p.1 i*T (-x+w-a)) • _=(coupon g S σ p.1 i*T (-a+(w-x))) • _; rw [show -a+(w-x) = -x+w-a by abel]
lemma Φ_probe (x y:Cover)(a b:Axis)(p:Name G)(j:G.ColorIndex): handshake (Trace.touch x a b [] j) (cable g S σ p y)= χ p.2 j*(D a (Mn g S σ p.1 b) (x-y)- D b (Mn g S σ p.1 a) (x-y)):=by unfold handshake; rw [paid]; change crackle (F:=G.Color) a b _ x j=_; rw [crackle_ap]; simp only [PiLp.sub_apply, beacon,PiLp.smul_apply,smul_eq_mul,κ]; change _=_ * ((Mn g S σ p.1 b (x-y+_)- Mn g S σ p.1 b (x-y))-(Mn g S σ p.1 a (x-y+_)-Mn g S σ p.1 a (x-y))); simp [sub_add_eq_add_sub]; ring
end YM.XSpace.Relief
