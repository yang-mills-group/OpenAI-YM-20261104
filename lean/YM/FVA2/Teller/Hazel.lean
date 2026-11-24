import YM.FVA2.Lambda.Bounds
import YM.FVA2.Parity.Pole
/-!
# `rank = r + n` on dimensional classical insertion in the `Mob` representation

 Here `m` is arbitrary, and `bornTree` is for every input with the given
 `Gallery` property (bound with $i+n$ there). Necessary input before
 validating MS implementation with loop grading. z here is the SCALED coupling
 (separate from the z in Mass.lean for dimensional parameter of the mass restoration).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Teller.Hazel
open Function Filter Set Finset MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Landau MS.Landau.Detect MS.Koszul MS.Heat
open MS.Book MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire MS.Alps
open MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Hem MS.Hem.Mell MS.Dock MS.Train MS.Pearl MS.Halo
open _root_.YM.MS.Shine MS.Color Garment.Wave Garment.Wick Signal Book.Convolve
open MS.Emit MS.Local.Physical MS.Menus MS.Land MS.Mach MS.Motif.Literal MS.Lifting MS.Arts.Pilot
open Position Position.Glazer
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n m k:ℕ}{a b:Arts.L m}{L:Type}
-- urban scaling on field arguments keeps ranks independent of dimensional ζ. For tree rank.
abbrev tint (r:ℂ)(L:Type): Op L ℂ where
 toFun X w:= r^w.length * X w
 map_add' X Y:= by ext w; exact mul_add ..
 map_smul' i X:= by ext w; exact mul_left_comm ..
variable (r z:ℂ)
lemma tent (x y:Raw L ℂ)(p:Sector L) : tint r L (product p x y)= product p (tint r L x) (tint r L y):= by
 funext w; change r^w.length*_= _; rw [scattered,scattered];
 change r^w.length • allocate p (R:=ℂ) w _= _; rw [ ← map_smul ];
 apply scatter_congr; intro i j H; rw [← split_length H]; change _*_= (r^i.length*x i)*(r^j.length*y j); rw [pow_add]; ring -- syntax
lemma stage0 (x:Raw L ℂ)(h:rank n x): tint r L x=r^n • x:= by
 funext w; by_cases he:w.length=n; · change r^(_)*_=_; rw [he]; rfl
 change r^w.length*x w= r^n*x w; rw [h w (by rw [mod_int]; omega), mul_zero,mul_zero]
local notation "H"=>tint r (Shore G m)
def maskG (r:ℂ)(G:Gauge): Mob G→ₗ[ℂ] Mob G where
 toFun F i:= tint r _ (F i)
 map_add' F Q:= funext fun i=> map_add (tint r _) (F i) (Q i)
 map_smul' c F:= funext fun i=>map_smul (tint r _) c (F i)
local notation "Ω"=> maskG r G
lemma luminous (a:Arts.L m)(F:Rack G m): H (rowP a F)=rowP a (H F):=by ext w; unfold tint; change r^w.length*((rowP a F) w)=_; simp only [rowP,moon]; change _*(_*_) = _ * (r^w.length*_); ring
lemma bp (a:Arts.L m)(i:G.ColorIndex): H ( A m G a i)= r • A m G a i:= by rw [stage0 _ (A m G a i) (n:=1) ( mon_leaf _ ),pow_one ]
lemma charm (a b:Arts.L m)(i:G.ColorIndex): H (cur z a b i)= r • cur (r*z) a b i:= by
    let Q:= quill a b (G:=G) i; simp only [cur, Pi.add_apply,Pi.smul_apply,map_add, map_smul ]; rw [ stage0 r _ ( n:=1) ( rank_α _ _ _ ),stage0 r (jaw G m (A m G a) (A m G b) i) ( n:=2 ) ( twoQ _ _ _ ),pow_one,smul_add,smul_smul,smul_smul]; congr 2; ring
lemma valence (a:Arts.L m)(F V: Mield G m)(h:∀ i,H ( F i )= r • V i)(i:G.ColorIndex) : H ( jaw G m (A m G a) F i )= r^2 • jaw G m (A m G a) V i:= by
    rw [chew,chew,map_sum]; simp_rw [map_sum,map_smul,Finset.smul_sum,smul_comm (r^2) ]; refine Finset.sum_congr rfl (fun i' _=> Finset.sum_congr rfl fun j _=>?_); refine congr_arg ( _ • · ) ?_; change H ( product (field Landau.parity) _ _)= r^2 • product _ _ _; rw [tent r, bp, h,map_smul,map_smul,LinearMap.smul_apply,smul_smul,pow_two]
lemma path (a:Arts.L m)(F V: Mield G m)(h:∀ i,H ( F i )= r • V i)(i:G.ColorIndex) : H (convoke z a F i)= r • convoke (r*z) a V i:= by
    simp only [convoke,LinearMap.add_apply, LinearMap.smul_apply, Pi.smul_apply, Pi.add_apply,map_add,map_smul, valence r a F V h i ]; unfold axisP; rw [lock,lock,luminous,h,map_smul, smul_add,smul_smul,smul_smul]; congr 2; ring
lemma pole (i j:Axis)(l:List Axis)(p:G.ColorIndex): H ( Pole G m i j z l p )= r • Pole G m i j ( r*z ) l p:= by
    induction l generalizing p with| nil=> exact charm _ _ _ _ p| cons a l ih=> exact path r z _ _ _ ih p
lemma wing (n:ℕ)(l:Fin n→Plaq)(i:Grid G n): Ω ( Pole.wing n l i z)= r^n • Pole.wing n l i (r*z):= by
    funext m; induction n with
    | zero=> exact ( stage0 r _ (n:=0) ( Rails.coin 1 ) )
    | succ n ih=>
       change tint r _ (product (field Landau.parity) (Pole_leaf z (l 0) (i 0)) ( Pole.wing n (l∘Fin.succ) (i∘Fin.succ) z m )) = r^(n+1) • product (field Landau.parity) _ _; rw [tent r,show tint r _ (Pole_leaf (n:=m) z (l 0) (i 0)) = _ from pole r z (m:=m) (l 0).i (l 0).j (l 0).jets (i 0), show tint _ _ ( Pole.wing n _ _ _ _) = _ from ( show tint _ _ _= r^n • Pole.wing n (l∘Fin.succ) (i∘Fin.succ) (r*z) m from ih (l∘Fin.succ) (i∘Fin.succ)), map_smul,map_smul,LinearMap.smul_apply,smul_smul,pow_succ ]; rfl
lemma current (i d:ℕ)(f:ℂ→ Mob G)(Y:f∈ Gallery G i d)(z:ℂ): Ω (f z)= r^i • f (r*z):= by
    refine Submodule.span_induction (R:=ℝ) (p:=fun f _=> Ω (f z)= r^i • f (r*z)) ?_ ?_ ?_ ?_ Y
    · rintro _ ⟨l,a,h,rfl⟩; unfold Pole.saint; simp only [map_sum,map_smul,wing,Finset.smul_sum]; exact Finset.sum_congr rfl fun j _=> smul_comm ..
    · simp only [Pi.zero_apply,map_zero,smul_zero]
    · rintro i j h k he hv; simp only [Pi.add_apply,map_add,he,hv,smul_add]
    rintro c x h hx; simp only [Pi.smul_apply,show Ω ( c • x z )= c • Ω (x z) from map_smul ((Ω).restrictScalars ℝ) c _, hx, smul_comm c (r^i)]
local notation "Ω'"=> Parity.Optic.mutt (fun n:ℕ=> maskG r G)
abbrev shift (r:ℂ)(p:ℕ)(G:Gauge):= Parity.Optic.mutt (fun n:ℕ=> (r^(p+n)) • (LinearMap.id: Mob G→ₗ[ℂ] Mob G) )
lemma owns (i d:ℕ)(x:Box (Mob G)) (h:(fun z=> value ( Mob G ) z x)∈ Gallery G i d) : Ω' x= shift r i G x:= by
    let S:=shift r i G; let A:= value ( Mob G ); apply OpenAxis.ticket_eq; intro z; have he(y:Box (Mob G)): A z (Ω' y)= Ω ( A z y ):= by
       induction y using Finsupp.induction_linear with | zero=> simp only [map_zero]| add i j h hu=> simp only [map_add,h,hu]| single k a=> unfold Parity.Optic.mutt A; rw [Finsupp.lsum_single]; dsimp only [LinearMap.comp_apply,Finsupp.lsingle_apply]; rw [value_sl,value_sl,map_smul]
    have hf(y:Box (Mob G)): A z (S y) = r^i • A (r*z) y := by
       induction y using Finsupp.induction_linear with | zero=> simp only [map_zero,smul_zero]| add i j h hu=> simp only [map_add,smul_add,h,hu]| single k a=> unfold S A shift Parity.Optic.mutt; rw [Finsupp.lsum_single]; dsimp only [LinearMap.comp_apply,Finsupp.lsingle_apply, LinearMap.smul_apply, LinearMap.id_apply]; rw [value_sl,value_sl,mul_pow,smul_smul,smul_smul,pow_add]; ring_nf
    exact (he x).trans ((current r i d _ h z).trans (hf x).symm)
lemma bornTree (i d:ℕ)(x:Box (Mob G)) (h:(fun z=> value ( Mob G ) z x)∈ Gallery G i d) : Book.rank (i+n:ℤ) ( x n m ):= by
    intro w he; by_contra! hh; rw [mod_int] at he; let r:ℂ:=2; obtain hx := congr_arg (fun y:Box (Mob G)=> y n ) ( owns r i d x h ); obtain hp:= Parity.Optic.standing (fun n=>maskG r G) x n; rw [hp] at hx; obtain hz: tint r (Shore G m) (x n m)= r^(i+n) • (x n m) := Eq.trans (congr_fun hx m) (congr_fun ( Parity.Optic.standing .. ) m) ; have hV : r^w.length=r^(i+n):=mul_right_cancel₀ hh (congr_fun hz w); unfold r at hV; norm_cast at hV; obtain hl:= Nat.pow_right_injective (a:=2) (by decide) hV; omega
end YM.FVA2.Teller.Hazel
