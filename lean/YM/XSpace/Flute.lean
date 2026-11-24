import YM.XSpace.Whist
/-!
# Concrete marks and paths (rotated towers at each play)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Relief Season Gland Chart2 Chiral Sail Octave Lattice Graph3 Mu MvPolynomial Asymptotics
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{u v b:E4}{x y z:ι→Cover}{G:Gauge}{i:ℕ}{W:Initialize G}
structure Player (W:Initialize G) where
  elem : Name G
  σ : Bool
  d : ℕ
  hr : 2 ≤ d
abbrev mum (W:Initialize G)(p:Name G) : Player W:= ⟨p,true,6,by norm_num⟩
abbrev mrs (W:Initialize G)(p:Name G): Player W:= ⟨p,false,4,by norm_num⟩
namespace Player
variable (i j:Player W)(g:G.Simple)
abbrev size := W.surveys i.d
abbrev M := Mn g i.size i.σ i.elem.1
abbrev gCost (x: Axis) := Season.line i.σ i.elem.1 x -- order
abbrev origin := wickLine g i.size i.σ i.elem
abbrev ask (x:Cover):Line G:= cable g i.size i.σ i.elem x
abbrev color : G.ColorIndex := i.elem.2
abbrev row : P:= i.elem.1
lemma visit : i.origin g ∈ cane 1 G:= carriesL g i.size i.σ i.elem
abbrev fare (x y: Cover):ℂ:= col (i.ask g x) (j.ask g y)
abbrev quote (u:E4): ℂ:= (↑(χ j.color i.color * surfT i.σ j.σ i.row j.row u):ℂ)
variable {x' y': Cover}
lemma α₀ (t:Axis) : i.M g t∈ Terrain 3:= shared g i.size i.σ i.row t
lemma α₁ (t:Axis) : i.M g t-field i.σ i.row t∈Terrain 4:=surfaces (stashed g i.size i.σ _ i.hr t)
variable {c:Shade.Cut} (p: Captain c L a x y z u v b)
include p in
lemma credited (t:Axis) : Payout L a 3 (fun j=> i.M g t (x j-y j)) (i.gCost t (u-v)):= Payout.of_shift (shore i.σ _ t) (i.α₁ g t) p.led p.both p.diff
include p in
lemma quoted : Named L a 4 (fun k=> fare i j g (x k) (y k)) (i.quote j (u-v)):=by
  unfold fare ask col quote; simp_rw [cup]; apply Named.coe; let h:= Payout.of_shift (charted i.σ j.σ i.row j.row) (surfaces (phrase g i.size j.size i.hr j.hr i.σ j.σ i.row j.row)) p.led p.both p.diff; exact (h.const_mul _).congr fun k=>mul_left_comm ..
include p in
lemma receipt (h:i.σ=j.σ) : funds L a 5 (fun k=> i.fare j g (x k) (y k)):=by unfold fare ask col; rw [h]; apply painted; exact duty g i.size p.led p.both p.diff j.size j.σ _ _ i.hr j.hr
include p in
lemma starter : funds L a 4 (fun k=> i.fare j g (x k) (y k)):= fare_stake p.led (i.origin g) (j.origin g) (i.visit g) (j.visit g) p.sec -- order
abbrev handshake₀ (x y:Cover)(u:Axis)(k:G.ColorIndex):= handshake (needle ((x,u),k)) (i.ask g y)
lemma handshake_pin (x y:Cover)(u:Axis)(k:G.ColorIndex): handshake₀ i g x y u k=i.M g u (x-y)*χ i.color k:=by rw [handshake₀,handshake,probes]; change bake (cable ..) (x,u) k=_; rw [beacon]; exact congr_arg (_*·) (κ i.color k)
-- derivative-less Ward values don’t commute automatically with covariance. Use volume explicitly.
local notation "K[" v "]"=> Trace.volume v
lemma rootleg (x: Cover)(σ:Bool)(p:Name G):K[x] (starlit σ p)= harp (Relief.core σ p.1 p.2 x):=by
  rw [harping,rings]; unfold core; simp only [_root_.map_sum,map_smul, brush, zero_add]
lemma arrow (x:Cover)(i:Axis)(p:G.ColorIndex):K[x] (av i p)=harp (needle ((x,i),p)):=by rw [av,Trace.volume, rename_X,harps]; simp [radius]
end Player
end YM.XSpace.Finale
