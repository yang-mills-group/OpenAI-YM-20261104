import YM.X.Local.Sleeve
/-!
# Twist mark at tilted moment. root costs. Reliable (limit) only, no analytic-in-cutoff required.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crystal
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Stems Hinge Clove Haze Grow Shelf Ocean Fielding CellsInt
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d:ℕ}{G:Gauge}{R r:ℝ}
local notation "K"=>Curly G
local notation "e"=>epsilon q
variable (A: Okay G k) (x: Long G)
lemma strike_word (z:List (Bone G (Reed.Horizontal G))) : tilt (str (phase A)) (playB z)∈verse ⊤ ((feelB z)-(k+1)):= by
    induction z with
    | nil=> rw [playB,List.map_nil,List.prod_nil,Derivation.map_one_eq_zero]; exact Submodule.zero_mem _
    | cons i l IH=>
       let n:=i.k+1; let R:=playB l; let s:=feelB l; let T:= Reed.Horizontal G; let a:=n+s-(k+1); let p:=glyph (com i.x); let g:= tilt (str (phase A)); change g (p*R)∈verse ⊤ a; rw [g.leibniz]; refine Submodule.add_mem _ (weaken_v (n:=n+(s-(k+1))) ?_ ?_) (weaken_v (n:=s+(i.k-(k+1)+1)) ?_ ?_)
       · unfold a; omega
       · exact verse_mul (n:=n) (k:=s-(k+1)) ⊤ (verse_glyph i.order (by simp)) IH
       · unfold a n; omega
       · exact verse_mul (n:=s) (k:=i.k-(k+1)+1) ⊤ (tier_v (n:=s) (T:=T) (by simp) (play_verse (p:=l) le_rfl)) (by unfold g p; rw [read_mess]; exact verse_glyph (k:=i.k-(k+1)) (grad_tilt A i.x i.order) (by simp))
lemma tilted (p:Curly G)(h:p∈verse (Reed.Horizontal G) n): tilt (str (phase A)) p∈ verse (G:=G) ⊤ (n-(k+1)):= by
   induction h using Submodule.span_induction with
   | mem x h=> obtain ⟨l,h,rfl⟩:=h; exact weaken_v (Nat.sub_le_sub_right h _) (strike_word A l)
   | zero=>rw [map_zero]; exact Submodule.zero_mem _
   | add a b h g x y=> rw [map_add]; exact Submodule.add_mem _ x y
   | smul a x h p=> rw [Derivation.map_smul]; exact Submodule.smul_mem _ _ p
variable {T:Submodule ℝ (Fan G)}
lemma still_play (l:List (Bone G T)): Strong (vapor G) (feelB l) (trumpet (Okay G) (valP (G:=G)) d (playB l)):= by
   induction l with
   | nil=> exact Strong.first
   | cons p l IH=> change Strong _ (tipB p+feelB l) (trumpet (Okay G) (valP (G:=G)) d (docB p*playB l)); rw [map_mul]; exact (show Strong _ (p.k+1) (trumpet (Okay G) (valP (G:=G)) d (docB p)) from by unfold docB; rw [tru]; exact bulges p.order d).multiply IH
lemma still_v {p:Curly G}(h:p∈verse T n): Strong (vapor G) n (trumpet (Okay G) (valP (G:=G)) d p):= by
   induction h using Submodule.span_induction with
   | mem p h=> obtain ⟨l,h,rfl⟩:=h; exact Strong.weaken (still_play l) h
   | zero=> rw [map_zero];exact Strong.zero
   | add a b p q u t=> rw [map_add]; exact u.add t
   | smul a i h p=> rw [map_smul]; exact p.scale a
lemma absent_boost (P:Word G)(h:m+(k+1)<P.d): clockLeaf (d:=d) m x (tilt (str (phase A)) (looking P))=0:= by
   let v:= (trumpet (Okay G) (valP (G:=G)) d) (tilt (str (phase A)) (looking P)); let a:= P.d-(k+1); change probeL x (Clove.leaf (vapor G) m v)=0; have he: Strong (vapor G) a v:= still_v (tilted A (looking P) (press_word P)); rw [← leaf_level (vapor G) v m le_rfl, he.none (by omega)]; unfold Clove.leaf; rw [map_zero,map_zero]
lemma fat (L:Curly G→ₗ[ℂ] ℂ){p:ℕ→ Curly G}{T:Submodule ℂ (Curly G)}(h:p∈Badge (Curly G) (Vanished q) T) : Vanished q (fun i=> L (p i)):= by
   induction h using Submodule.span_induction with
   | mem p h=> obtain ⟨c,x,h,ht,rfl⟩:=h; simp_rw [map_smul]; exact Vanished.left h (Charged.constant (L x)) -- p*x
   | zero=> simp_rw [Pi.zero_apply,map_zero]; exact Vanished.zero
   | add a b h p x y=> simp_rw [Pi.add_apply,map_add]; exact x.add y
   | smul a b h x=> simp_rw [Pi.smul_apply,map_smul]; exact Vanished.right (Charged.constant a) x
include hq
variable (P:Word G)
lemma clock_l (L:Curly G→ₗ[ℂ] ℂ)(a:ℤ): Released (fun i=> (e i)^a • L (load q P i-looking P)):= late hq (eps_supp (fat L (self_ration hq P)))
lemma clock_unite (L:Curly G→ₗ[ℂ] ℂ)(a:ℤ)(h:a≠0→L (looking P)=0): Released (fun i=> (e i)^a • L (load q P i)):= by
    have he : (fun i=>e i ^ a • L (load q P i))=(fun i=>e i ^ a • L (load q P i-looking P)) + fun i=>e i ^ a • L (looking P):= funext (fun i=>by rw [Pi.add_apply]; simp only [map_sub,smul_sub,sub_add_cancel])
    rw [he]; apply Released.add (clock_l hq P L a); by_cases hp:a=0; · rw [hp]; simp only [zpow_zero,one_smul];exact constell _
    rw [h hp]; simp only [smul_zero]; exact Released.zero
set_option maxHeartbeats 600000 in
lemma clock_released (h:m+(k+1)≤P.d): Released (fun i=> ((e i) ^ (((k+1+m:ℕ):ℤ)-P.d)) • clockLeaf (d:=d) m x (tilt (str (phase A)) (load q P i))):= by
   let L₀:= (clockLeaf (d:=d) m x).comp (tilt (str (phase A))).toLinearMap; let b:=(((k+1+m:ℕ):ℤ)-P.d); change Released (fun i=> (e i)^b • L₀ (load q P i)); apply clock_unite hq P L₀ b; intro hv; have hs : m+(k+1)<P.d:= (by unfold b at hv; omega); have he := absent_boost (d:=d) A x P hs; exact he
end YM.PositionX.Crystal
