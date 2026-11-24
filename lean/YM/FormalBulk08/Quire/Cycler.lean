import YM.FormalBulk08.Quire.Bear
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {X I : Type*} {Y U:X→Type*} {V:Type*}{r m n:ℕ} {η σ A B C α β:ℝ}
lemma stove {T S:Tile V (r+1+1)}{q Q: V→V→ℝ}{D:Reach V}{o:V}(h:Knoxville D η o T A)(hp: Knoxville D η o S B)(hs:0≤η)(he:∀ i j,‖q i j‖≤C)(hg:∀ i j,‖Q i j‖≤ α)(hC:0≤C)(hk:0≤α) : stare q T-stare Q S= stare q (T-S)+stare (q-Q) S:= by
   have hT := fund_stare h hs he hC; have hS:=fund_stare hp hs hg hk; have hM:= fund_stare (penn_sub h hp) hs he hC; have hR:= fund_stare (q:=q-Q) hp hs (fun i j=>(norm_sub_le (q i j) (Q i j)).trans (add_le_add (he i j) (hg i j))) (add_nonneg hC hk)
   funext v; rw [Pi.sub_apply, Pi.add_apply]; change (∑' i,telescopeTerm q T v i)-(∑' i,telescopeTerm Q S v i)=(∑' i,telescopeTerm _ (T-S) v i)+(∑' i,telescopeTerm _ _ v i)
   rw [← Summable.tsum_sub ((hT.points hs v).of_norm) ((hS.points hs v).of_norm), ←Summable.tsum_add ((hM.points hs v).of_norm) ((hR.points hs v).of_norm)]; refine tsum_congr fun i=>?_ ; unfold telescopeTerm Lava.shed halve;dsimp;ring
lemma grates_diff {T S:Tile V (m+1)}{K N:Tile V (n+1)}{q Q: V→V→ℝ}{D:Reach V}{o:V}{θ θ':ℝ}(h:Bail D η T A)(hp:Bail D η S B)(he:Knoxville D η o K C)(hb:Knoxville D η o N α)(hg:Grate D η (fun i j=> q j i) θ)(hx:Grate D η (fun i j=>Q j i) θ')(hw:Grate D η (fun i j=> (q-Q) j i) β)(hs:0≤η):
    bond q T K-bond Q S N= bond q (T-S) K+bond q S (K-N)+bond (q-Q) S N := by
    funext v; have A:= (funded_cross (q:=q) hg hs h he).points hs v|>.of_norm;have B:=(funded_cross (q:=Q) hx hs hp hb).points hs v|>.of_norm
    have C:= (funded_cross (q:=q) hg hs (h.sub hp) he).points hs v|>.of_norm; have E:= (funded_cross (q:=q) hg hs hp (penn_sub he hb)).points hs v|>.of_norm;have F:= (funded_cross (q:=q-Q) hw hs hp hb).points hs v|>.of_norm
    simp only [Pi.add_apply,Pi.sub_apply]
    change (∑' i,weld q T K v i)-(∑' i,weld Q S N v i)= (∑' i,weld q (T-S) K v i)+(∑' i,weld q S (K-N) v i)+(∑' i,weld (q-Q) S N v i)
    rw [← C.tsum_add E, ← A.tsum_sub B, ← (C.add E).tsum_add F]; exact tsum_congr fun i=>by unfold weld Lava.shed clutch halve; dsimp;ring

variable {τ:Time X}{R:∀ x, Reach (Y x)}{o:∀ i,U i→Y i}{η δ: X→ℝ}{b:∀ i,U i→ℝ}{q Q:∀ x:X,Y x→Y x→ℝ}
lemma Bear.bake {T:∀ x:X,U x→Tile (Y x) (r+1+1)} (h: Bear τ R o η b T)(hs:∀ i,0≤η i)(hq: Aster.Silver τ R η q) : Bear τ R o η b (fun i p=>stare (q i) (T i p)) := by
    obtain ⟨C,hC,c,H⟩:= h; obtain ⟨-,A,hA,X⟩:=hq; let n:ℝ:=1/2*(r+2)*(r+1);have hn:0≤n:=by unfold n; positivity
    refine ⟨_, (soft_coin τ n).times (hA.times hC),fun i=>mul_nonneg hn (mul_nonneg (X i).1 (c i)),fun i p=>?_⟩; convert knox_stare (q:=q i) (H i p) (hs i) ((X i).rough (hs i)) (X i).1 using 1;unfold n; ring
lemma Matched.bake {T S:∀ x:X,U x→Tile (Y x) (r+1+1)} (h:Matched τ R o η δ b T S)(hs:∀ i,0≤ η i)(hp:Gilt τ R η δ q Q): Matched τ R o η δ b (fun i p=> stare (q i) (T i p)) (fun i p=> stare (Q i) (S i p)):= by
    obtain ⟨C,hC,c,H⟩:=h.left; obtain ⟨B,hB,b_,He⟩:=h.right; obtain ⟨A,hA,a,V⟩:=hp.haze;obtain ⟨-,E,hE,W⟩:= hp.left;obtain ⟨-,Y,h,Y1⟩:=hp.right
    have hP:Bear τ R o η (fun i p=>δ i*b i p) (fun i p=> stare (q i-Q i) (S i p)):= by
       let n:ℝ:=1/2*(r+2)*(r+1); refine ⟨_, (soft_coin τ n).times (hA.times hB),fun i=>mul_nonneg (by unfold n; positivity) (mul_nonneg (a i) (b_ i)),fun i p=>?_⟩; convert knox_stare (q:=q i-Q i) (He i p) (hs i) ((V i).rough (hs i)) (V i).1 using 1; unfold n; ring
    have hM : Matched τ R o η δ b T S := by assumption
    refine ⟨hM.left.bake hs hp.left,hM.right.bake hs hp.right,?_⟩; convert (hM.chalk.bake hs hp.left).plus hP using 1; exact funext fun i=>funext fun p=> stove (H i p) (He i p) (hs i) ((W i).rough (hs i)) ((Y1 i).rough (hs i)) (W i).1 (Y1 i).1
variable {T S:∀ i:X,Tile (Y i) (m+1)}{Z W:∀ i:X,U i→ Tile (Y i) (n+1)}
lemma Bear.bond (ht:Cost τ R η T)(h:Bear τ R o η b Z)(hp:Aster.Silver τ R η q)(hs:∀ i,0≤ η i) : Bear τ R o η b (fun i p=> Lava.bond (q i) (T i) (Z i p)):= by
    obtain ⟨C,hC,H⟩:=ht; obtain ⟨A,hA,a,W⟩:=h; obtain ⟨hv,E,e,V⟩:=hp;let x:ℝ:=1/2*(m+1)*(n+1);refine ⟨_,(soft_coin τ x).times ((hC.times e).times hA),fun i=>mul_nonneg (by unfold x; positivity) (mul_nonneg (mul_nonneg (H i).1 (V i).1) (a i)),fun i p=>?_⟩;convert knox_bond (q:=q i) ((V i).turn (hv i)) (hs i) (H i) (W i p) using 1;unfold x; ring
lemma Matched.bond (hp: Totem τ R η δ T S)(h: Matched τ R o η δ b Z W)(hg:Gilt τ R η δ q Q)(hs:∀ i,0≤η i): Matched τ R o η δ b (fun i p=>Lava.bond (q i) (T i) (Z i p)) (fun i p=>Lava.bond (Q i) (S i) (W i p)):= by
    obtain ⟨C,hC,H⟩:=hp.left; obtain ⟨E,e,F⟩:=hp.right; obtain ⟨A,hA,a,M⟩:=hp.nebula; obtain ⟨B,hB,b_,X⟩:=h.left;obtain ⟨J,j,u,Y⟩:=h.right; obtain ⟨v,K,hk,V⟩:=hg.left; obtain ⟨y,D,d,P⟩:=hg.right; obtain ⟨N,t,n_,F'⟩:= hg.haze
    have he x i j : (q x-Q x) i j= (q x-Q x) j i:= by simp [v x i j,y x i j]
    let U i p:= δ i*b i p; let x:ℝ:= 1/2*(m+1)*(n+1); have hh:0≤x:=by unfold x; positivity
    have ha: Bear τ R o η U (fun i p=>Lava.bond (q i) (T i - S i) (Z i p)):= by
       refine ⟨_,(soft_coin τ x).times ((hA.times hk).times hB),fun i=>mul_nonneg hh (mul_nonneg (mul_nonneg (a i) (V i).1) (b_ i)),fun i p=>?_⟩; convert knox_bond (q:=q i) ((V i).turn (v i)) (hs i) (M i) (X i p) using 1;unfold U x; ring
    have hn: Bear τ R o η U (fun i p=> Lava.bond (q i - Q i) (S i) (W i p)):= by
       refine ⟨_,(soft_coin τ x).times ((e.times t).times j),fun i=>mul_nonneg hh (mul_nonneg (mul_nonneg (F i).1 (n_ i)) (u i)), fun i p=>?_⟩; convert knox_bond (q:=q i-Q i) ((F' i).turn (he i)) (hs i) (F i) (Y i p) using 1; unfold x U; ring
    refine ⟨Bear.bond hp.left h.left hg.left hs,Bear.bond hp.right h.right hg.right hs,?_⟩; convert (ha.plus (Bear.bond hp.right h.chalk hg.left hs)).plus hn using 1; exact funext fun i=>funext fun p=>grates_diff (H i) (F i) (X i p) (Y i p) ((V i).turn (v i)) ((P i).turn (y i)) ((F' i).turn (he i)) (hs i)
end YM.FormalBulk08.Quire
