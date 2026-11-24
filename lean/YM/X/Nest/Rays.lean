import YM.X.Nest.Shelved
import YM.X.Fill.Kite
/-!
# Rays in lifted Tome of masses. Uniform precision from user-chosen sequence tag.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate.Rays
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {V I T:Type*} {i k d:ℕ} {G:Gauge}
variable {q:ℕ+} (hq:1<q.val)(α:T→ℕ) (x y:Fielding.Walk)(p:Word G) {U W:E4}
abbrev travelers (α:T→ℕ)(q:ℕ+) (G:Gauge):= fun t:T=> flow G (side q (α t))
def token : Subalgebra ℂ (T →ℂ) where
    carrier:= {c|∃ b:ℕ→ℂ,Released b∧ c=b ∘ α}; mul_mem' {x y} hp hc:= by obtain ⟨c,h,rfl⟩:=hp; obtain ⟨b,hb,rfl⟩:=hc;exact ⟨_,breaths h hb,rfl⟩
    add_mem' {x y} hp hc:= by obtain ⟨c,h,rfl⟩:=hp; obtain ⟨b,hb,rfl⟩:=hc; exact ⟨_,h.add hb,rfl⟩
    algebraMap_mem' z:= ⟨_,constell z,rfl⟩
lemma rear (f:ℕ→ℂ)(h:Released f): (f ∘ α)∈ token α:=⟨f,h,rfl⟩
abbrev Stool (G:Gauge):= Bone G (Reed.Horizontal G)
def liftC (q:ℕ+)(α:T→ℕ)(x:Fielding.Walk)(B:Bone G (Reed.Horizontal G)): Stella (Hair G) T:= fun t=>com (tack B.k (epsilon q (α t)) (side q (α t)) (x (α t)) B.x)
def Meter (q:ℕ+)(α:T→ℕ)(x:Fielding.Walk)(G:Gauge): Set (Stella (Hair G) T):= range (liftC (G:=G) q α x)
lemma cost_unit (f g: Bone G (Reed.Horizontal G))(t:T) : cross (travelers α q G) (liftC q α x f) (liftC q α y g) t=((spend (side q (α t)) (x (α t)) (y (α t)) f.x g.x / ((epsilon q (α t)) ^ (2+(f.k+g.k))):ℝ):ℂ):= by
    let p:=epsilon q (α t); have hp:0<p:= epsilon_pos ..; unfold cross liftC; rw [cornered]; unfold tack; apply congr_arg Complex.ofReal; simp_rw [map_smul,← taste_eval,map_smul]; rw [taste_eval,← spent]; rw [show 2+(f.k+g.k)= f.k+1+(g.k+1) by omega,pow_add _ (f.k+1) (g.k+1)]; change (p^(g.k+1))⁻¹*((p^(f.k+1))⁻¹ * _)=_ / (p^(f.k+1)*p^(g.k+1)); field_simp
variable {x y}
include hq
lemma cost_paths (hf:plot q x U)(hg:plot q y W)(he:U≠W)(v:Stella (Hair G) T)(hv:v∈Meter q α x G)(u:Stella (Hair G) T)(hu:u∈Meter q α y G): cross (travelers α q G) v u ∈ token α:= by
   obtain ⟨t,rfl⟩:=hv; obtain ⟨p,rfl⟩:=hu; let f(n:Side)(x y:Cover):= spend n x y t.x p.x; have h : Released (fun i=> f (side q i) (x i) (y i)/ (epsilon q i)^(2+(t.k+p.k))):= Print.glides hq (enrolled₂ t.x p.x t.order p.order) he hf hg; exact ⟨_,Released.lin Complex.ofRealCLM.toLinearMap h, funext fun k=> cost_unit α x y t p k⟩ -- scale cost accepts q implicit? 
omit hq
variable (x)
lemma piece_at (q:ℕ+) (p:Stool G)(i:T): dress (x (α i)) (docB p)= ((epsilon q (α i) )^(p.k+1)) • (piece (liftC q α x p) i):= by
    let a:= epsilon q (α i); have hp : 0<a:= epsilon_pos ..; unfold docB; rw [dress_glyph, piece, comp_apply,liftC]; unfold tack; rw [com_text, com_text]; unfold blade; rw [map_smul, smul_smul,mul_inv_cancel₀ (pow_pos hp ..|>.ne'),one_smul]
lemma float_unit (q:ℕ+)(l:List (Stool G))(i:T): dress (x (α i)) (playB l)= (epsilon q (α i))^(feelB l) • (thing (l.map (liftC q α x)) i):= by
   induction l with
   | nil=> change dress _ 1=(_^ (0:ℕ):ℝ) • 1;rw [map_one,pow_zero,one_smul]
   | cons p l IH=> unfold playB; rw [List.map_cons,List.prod_cons,map_mul]; change _ * dress _ (playB l)= _^(tipB p + feelB l) • _;rw [piece_at (p:=p) (q:=q),IH,List.map_cons, thing_cons,Pi.mul_apply,smul_mul_assoc,mul_smul_comm, pow_add _ (tipB p) (feelB l), smul_smul];rfl
abbrev Carries (q:ℕ+)(α:T→ℕ)(x:Fielding.Walk)(p: Code (Hair G) T):= ∃ n,p∈ Bag (token α) (Meter q α x G) n
def urban (q:ℕ+)(α:T→ℕ)(p:Word G) (x:Fielding.Walk): Code (Hair G) T:=fun t=> epsilon q (α t) ^(-(p.d:ℤ)) • dress (x (α t)) (load q p (α t))
lemma Carries.add {x} {f g : Code (Hair G) T}(h:Carries q α x f)(hx: Carries q α x g): Carries q α x (f+g):=by obtain ⟨n,h⟩:=h; obtain ⟨k,hx⟩:=hx; exact ⟨max n k,Submodule.add_mem _ (promote _ _ (le_max_left ..) h) (promote _ _ (le_max_right ..) hx)⟩
lemma transporting {f:Curly G}(h:f∈verse (Reed.Horizontal G) k) : -- for unscaled → Weight after
    1<q.val → Carries q α x (fun i=> epsilon q (α i) ^(-(k:ℤ)) • dress (x (α i)) f):= by
    intro hq; induction h using Submodule.span_induction with
    | mem p h=>
       obtain ⟨l,h,rfl⟩:=h; simp_rw [float_unit α x q l]; let v:= l.map (liftC q α x); let f(i:ℕ):=epsilon q i^(feelB l - k); let p(i:T):ℂ:= Complex.ofReal (f (α i)); refine ⟨l.length,?_ ⟩;
       have he (i): epsilon q i ^(-(k:ℤ))*epsilon q i ^feelB l= f i:= by unfold f;rw [← zpow_natCast,← zpow_add₀ (epsilon_pos q _).ne', show (-(k:ℤ))+ (feelB l)= ↑(feelB l-k : ℕ) by omega, zpow_natCast]
       rw [show (fun i=> _ • (_ • _))= charge p*thing v from ?_]; swap; · rw [unify]; ext1 i; rw [smul_smul,he];exact RCLike.real_smul_eq_coe_smul (K:=ℂ) ..
       apply Bag.point
       · apply Bag.necklace; · intro b hb; obtain ⟨t,ht,rfl⟩:= List.mem_map.mp hb; exact ⟨t,rfl⟩
         simp [v]
       exact rear α (Complex.ofReal ∘ f) (Released.lin Complex.ofRealCLM.toLinearMap (show Released f from ⟨(0:ℝ)^((feelB l)-k),(paths hq).cutoff.pow _⟩))
    | zero=> refine ⟨0,?_⟩; simp_rw [map_zero,smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ih ih'=> simp only [map_add,smul_add]; exact Carries.add α ih ih'
    | smul a b _ ih=> obtain ⟨m,h⟩:=ih;refine ⟨m,?_⟩; simp_rw [map_smul,smul_comm (_:ℝ) a]; exact Submodule.smul_mem _ a h
end YM.PositionX.Crate.Rays
