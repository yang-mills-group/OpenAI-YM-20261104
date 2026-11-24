import YM.FVA2.Teller.States
/-!
 # Physical and exact primitive outputs respect the SAME symmetries including rank parity

 $b=true$ required for further strict representation D. (see `Teller/Where`). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Teller.Homes
open Function Set Filter Finset MeasureTheory Metric Real
open Lattice MS MS.Plane MS.Koszul MS.Heat MS.Plane.Flux MS.Landau MS.Arts MS.High MS.High.Knobs
open MS.Local.Physical MS.Menus MS.Land MS.Lifting MS.Native MS.Native.Orient MS.Native.Chart MS.Cylinder MS.Cylinder.Lab
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Wind MS.Wind.Leading
open Position Position.Wheel Position.Axes Position.Favors Ace Parity Capacity Desk
open MS.Native.Paint Register
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n d k r:ℕ}{B:Deck G} {J:Glyph B d}{b:Bool}{I:Type}{u:ℤ}
local notation "℘"=> Press.portDeck G
local notation "γ"=> Parity.Screen.grey G Cover
variable {P:Acts (Press.portDeck G) d}{F:DMark G d→Acts (Press.portDeck G) d}
variable (s t: Signed) (F) (z:ℝ) (y:DMark G d)
-- primitive.Exact input tier. Convenient domain log-length
abbrev tall (F:DMark G d→Acts (Press.portDeck G) d)(n:ℕ)(z:ℝ)(y:DMark G d) := (F y n).proof.input z
def Hcover (F:DMark G d→Acts (Press.portDeck G) d) := ∀ (s:Signed) n (z:ℝ) y,Favors.move s (tall F n z) y= pose s (tall F n z y)
lemma move_m {E:Type}[AddCommGroup E][Module ℝ E](L:E→ₗ[ℝ] E)(f:DMark G d→ E)(x:DMark G d): L (move s f x)= move s (fun i=> L (f i)) x:= by unfold move; simp_rw [map_sum,map_smul]
lemma shuttle : tall (divert s F) n z y= pose s ( move s⁻¹ (tall F n z) y ):= by
 rw [tall,divert, current]; unfold move; rw [map_sum]; apply Finset.sum_congr rfl; intro i _; exact (map_smul ( (pose (G:=G) (R:=ℤ) s ).restrictScalars ℝ ) ( markS s⁻¹ G d y.1.val y.2 i ) ( tall F n z ( pin y i ) ) ).symm
lemma flow_move : move t (tall (divert s F) n z) y= pose t ( tall (divert (t⁻¹*s) F) n z y ):= by
    let f:=(pose (G:=G) (R:=ℤ) s).restrictScalars ℝ; let Q:=tall F n z; rw [ show tall (divert s F) n z=(fun i=>f (move s⁻¹ Q i)) from funext ( fun i=>Homes.shuttle (s:=s) (F:=F) (z:=z) (y:=i) (n:=n)), ← move_m t f, move_l, Homes.shuttle, mul_inv_rev, inv_inv ]; rw [show ∀ x,f x=pose s x from fun _=>rfl,pose_mul,mul_inv_cancel_left]
lemma company : Hcover ( aspired F ):= by
    intro s n z y; let M(s:Signed):=tall (divert s F) n z; have H(x:DMark G d): tall ( aspired F ) n z x=∑ s:Signed, θ • M s x:= current ..
    rw [funext H]; dsimp only; rw [ Favors.move_sum,map_sum ]; simp_rw [ show ∀ x:Dot G Cover, (pose s) ( θ • x )= θ • pose s x from fun x=> map_smul ((pose s).restrictScalars ℝ) θ x ]; apply Fintype.sum_equiv (Equiv.mulLeft s⁻¹); intro i; exact congr_arg (θ • ·) ( flow_move F i s z _ )
lemma parity_tall : tall (fun i:DMark G d=> Screen.shaded i.1.val (F i)) n z y= Screen.sigma ( n+y.1.val ) • γ (tall F n z y):= by
    change (Screen.powered _ _).input z=_; rw [Screen.copes, ← Screen.sig]; rfl
variable (h:Hcover F)
lemma h_sum {S:Finset I}{F:I→ DMark G d→Acts ( Press.portDeck G ) d} (c:I→ℝ)(h:∀ i∈S,Hcover (F i)): Hcover (fun i=> stepF S c (fun j=> F j i)):= by
    intro s n z y; let X(j):= tall (F j) n z; have he(y:DMark G d): tall (fun i=> stepF S c (fun j=> F j i)) n z y=∑ j∈S,c j • X j y:= current ..
    rw [funext he]; dsimp only; rw [move_sum,map_sum]; apply Finset.sum_congr rfl; intro i hi; rw [show move s ( X i ) y=_ from h i hi s n z y]; exact (map_smul ( (pose (G:=G) (R:=ℤ) s ).restrictScalars ℝ ) _ _ ).symm
lemma commuted (h:Hcover F): Hcover (fun i:DMark G d=> Screen.shaded i.1.val (F i)):= by
    intro s n z y; simp_rw [funext fun x:DMark G d=> parity_tall (n:=n) F z x]; let p:= Screen.sigma (n+y.1.val); let θ:=γ; let X:= tall F n z; let L:= p • θ.restrictScalars ℝ
    have he: move s (fun i=> Screen.sigma (n+i.1.val) • γ ( tall F n z i)) y= L ( move s X y ):= by rw [move_m s L]; rfl
    rw [he, ( h s n z y : move s X y=_ )]; change p • θ (pose s _) =_; unfold θ; rw [commute,parity_tall]; exact (map_smul ((pose (G:=G) ( R:=ℤ ) s).restrictScalars ℝ) _ _ ).symm -- see
lemma covered (h:Hcover F): Hcover (fun i:DMark G d=>Screen.morn i (F i)):= by
   apply h_sum; intro i _; cases i; exact h; exact commuted _ h
-- parity weights including primitive.Lapl normalization.Exact. nothing smoothing. Existence follows.
lemma mow (A: Dot G Cover) : γ (γ A)=A:= by apply Subtype.ext; simp only [Screen.tag,Hue.stop];
lemma reflective (P:Acts (Press.portDeck G) d)(y: DMark G d)(n:ℕ)(z:ℝ): Hue.only (n+y.1.val) (( Screen.morn y P n).proof.input z).val:= by
 rw [Hue.test_p]; rw [ Screen.morn,current ]; rw [Fintype.sum_bool ]
 let A:= ( P n ).proof.input z; let k:= Hue.σ (n+y.1.val); let t:ℂ:=↑(( 2:ℝ )⁻¹)
 change Hue.flip _ ( t • ( Screen.powered (n+y.1.val) (P n).proof ).input z + t • A ).val= k • ( t • ( Screen.powered (n+y.1.val) (P n).proof ).input z + t • A ).val
 rw [Screen.copes, ← Screen.tag, ← Submodule.coe_smul]
 apply congr_arg Subtype.val; rw [map_add,map_smul,map_smul,map_smul, mow, smul_add,smul_comm _ k, smul_comm k t ]; simp_rw [smul_smul]; rw [mul_left_comm k t (Hue.σ (n+y.1.val)), ( show k * Hue.σ (n+y.1.val)=1 from Hue.s_id _ ),mul_one]; exact add_comm ..

lemma grow_reflect (P:Prescription ℘)(d:ℕ)(i:Plaid ℘ d)(n:ℕ)(z:ℝ) : Hue.only ( n+i.1.val ) ( ( (Screen.brush P).fees d i n).proof.input z).val:= reflective _ _ _ _
variable {S:Prescription (Press.portDeck G)}
lemma reserve (h:Sturdy S b): Sturdy ( Screen.brush ( amen (Norm₀ S))) b:= by
    intro d i; refine spice i ( show Houses (( amen (Norm₀ S)).fees d i) _ _ from ?_); cases d with| zero=> exact town i| succ d=> exact morph i (h _)
lemma currency : ∀ d,Hcover ((Screen.brush ( amen ( Norm₀ S ) )).fees d):=by
    intro d
    change Hcover (fun i=> Screen.morn i (( amen ( Norm₀ S ) ).fees d i ) ); refine covered _ ?_; cases d with
    | zero => intro s n z y; change move s (fun i=> ( active i n).proof.input z) y=pose s (( active y n).proof.input z); simp_rw [vatican]; rw [map_zero]; simp [move]
    | succ d=> change Hcover (aspired ( S.fees (d+1))); exact company _

end YM.FVA2.Teller.Homes
