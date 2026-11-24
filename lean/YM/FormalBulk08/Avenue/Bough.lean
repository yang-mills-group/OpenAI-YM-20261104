import YM.FormalBulk08.Avenue.Infinity

/-! Winding of conditional cover tensors rooted (mark not canonical free origin!),
including constants. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Avenue
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05
open Lotus Shore Mesa Gorge City Cork Rift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I V J : Type*} {m p r : ℕ} {η θ A B C : ℝ}

open Kemp
variable {x:Biglot I}[Fintype I]
lemma calm_stare {K : Tile (Biglot I) (r+1+1)} {T : (n:Side)→Tile (Tor n I) (r+1+1)}
    {q : Biglot I→ Biglot I→ℝ} {M : (n:Side)→ Tor n I → Tor n I → ℝ} (h : Kalm η x K T) (e : Wind q M) (C : ℝ)
    (hs : 0<η) (hp : ∀ᶠ n in atTop, 0≤ C∧∀ i j,‖M n i j‖≤C) : Kalm η x (stare q K) (fun n=>stare (M n) (T n)) := by
   obtain ⟨h,B,H⟩:=h; refine ⟨fun v=>?_,_,(H.and hp).mono fun n hh=> knox_stare hh.1 hs.le hh.2.2 hh.2.1⟩
   let R n := Lotus.drip n ∘ v
   let L:= size x.1
   let d := C*((r+2:ℕ):ℝ)*((r+1:ℕ):ℝ)
   let U (x : Biglot I × Biglot I) := Real.exp (η*L)*(d*B)* (coast (η/2) x.1*coast (η/2) x.2)
   obtain ⟨l,hl,hx⟩ := (H.and hp).exists
   have hb:=hl.1; have hh:=hx.1; have hd : 0≤d:=by unfold d;positivity
   refine jolt_limit (windup I I) (fun n=> telescopeTerm (M n) (T n) (R n)) (telescopeTerm q K v) U ((coast_pair (half_pos hs)).mul_left _) (fun _=> by unfold U coast;positivity) (height_pair h e v) ?_
   filter_upwards [H,hp] with n hn hm k
   let W : chain (Tor n I) (r+1+1):= Fin.cons k.2 (Fin.cons k.1 (R n)); let u:= Lotus.drip n x
   let S : chain (Tor n I) (r+1+1+1) := Fin.cons u W; let t:= wide (lake n I) S
   have he : skit n k.1.1 + skit n k.2.1 ≤ 2*t+2*L := by
      have hz (j : Fin (r+1+1)): skit n (W j).1 ≤ t+L:= (skit_anchor n S 0 j.succ).trans (Nat.add_le_add_left (skirt ..) t)
      have hu := hz 0; have hv:=hz (Fin.succ 0); have hh : skit n k.1.1≤t+L:=by simpa only [W,Fin.cons_succ,Fin.cons_zero] using hv
      change skit n k.2.1 ≤ t+L at hu; omega
   refine sloped L t n k.1 k.2 _ he ?_ hs.le
   have ho : ‖halve (M n k.1 k.2)*((r+2:ℕ):ℝ)* ((r+1:ℕ):ℝ)‖ ≤ d := by
       rw [norm_mul,norm_mul,half_norm,Real.norm_of_nonneg (show 0≤((r+2:ℕ):ℝ) by positivity),Real.norm_of_nonneg (show 0≤((r+1:ℕ):ℝ) by positivity)]; unfold d; gcongr
       have hh' := hm.2 k.1 k.2; rw [Real.norm_eq_abs] at hh' ⊢; linarith
   unfold telescopeTerm; rw [norm_mul,mul_left_comm]; exact mul_le_mul ho (palm hn W) (by positivity) hd
-- rank-only arrays for Hart. Exact orientation i=0 all ranks.

abbrev Beams (V:Type*) := (r:ℕ)→Tile V r
def bleat (q:V→V→ℝ)(A:Beams V):ℕ→Beams V
 | 0=> A
 | n+1=> fun r=> stare q (bleat q A n (r+1+1))
def pageant (q:V→V→ℝ)(A:Beams V)(n r:ℕ):= ∑ i∈Finset.range (n+1), ounce ℝ i • bleat q A i r
lemma bleat_live {q:V→V→ℝ}{A:Beams V}{u n:ℕ}(h:∀ m>u,A m=0)(he:bleat q A n r≠0):2*n+r≤u:= by
   induction n generalizing r with
   | zero=> rw [mul_zero,zero_add]; exact (show r ≤ u from Classical.byContradiction (fun hp=> he (h r (by omega))))
   | succ n ih=>
       have hx:= ih (r:=r+1+1) (fun hp=>he (show stare _ _= _ from hp ▸ stare_nil q _));omega
lemma recital {q:V→V→ℝ}{A:Beams V}{u n:ℕ}(h:∀ m>u,A m=0)(he:u < r): pageant q A n r=0:= Finset.sum_eq_zero fun i _=>by rw [show bleat q A i r=0 from Classical.byContradiction fun hx=>by have ht:=bleat_live h hx;omega,smul_zero]
lemma level_wind {q:Biglot I→Biglot I→ℝ}{M:(n:Side)→Tor n I→Tor n I→ℝ}{A:Beams (Biglot I)}{T:(n:Side)→ Beams (Tor n I)}(h:Wind q M) (hp: ∀ n, Kalm η x (A n) (fun i=>T i n))(he:∀ n i j, ‖M n i j‖≤B) (hs:0<η)(hh:0≤B) (N:ℕ): Kalm η x (bleat q A N r) (fun n=>bleat (M n) (T n) N r):= by
    induction N generalizing r with
    | zero=> exact hp r
    | succ n ih=> exact calm_stare ih h B hs (Eventually.of_forall fun i=>⟨hh,he i⟩)
lemma plaza_wind {q:Biglot I→Biglot I→ℝ}{M:(n:Side)→Tor n I→Tor n I→ℝ}{A:Beams (Biglot I)}{T:(n:Side)→ Beams (Tor n I)}(h:Wind q M) (hp: ∀ n, Kalm η x (A n) (fun i=>T i n))(he:∀ n i j, ‖M n i j‖≤B) (hs:0<η)(hh:0≤B) (N:ℕ): Kalm η x (pageant q A N r) (fun n=>pageant (M n) (T n) N r):= by
    unfold pageant; exact kalm_many _ (fun i _=>(level_wind h hp he hs hh i).smul _)
lemma pageant_growth {q:V→V→ℝ}{A:Beams V}{u n:ℕ}(h:∀ m>u,A m=0)(hu:u≤n):pageant q A n r=pageant q A u r:= by
    unfold pageant; symm; apply Finset.sum_subset (Finset.range_mono (by omega)); intro i hi h'; rw [show bleat q A i r=0 from ?_,smul_zero]; by_contra he; have hv:=bleat_live h he; have ht:=mt (Finset.mem_range).2 h';omega
lemma pageant_peak {q:V→V→ℝ}{A:Beams V}{u:ℕ}(h:∀ m>r,A m=0): pageant q A u r=A r:= by
    unfold pageant; rw [Finset.sum_eq_single 0]; simp only [ounce_zero,one_smul]; rfl
    · intro i _ hi; rw [show bleat q A i r=0 from Classical.byContradiction fun hx=>by have ht:=bleat_live h hx;omega,smul_zero]
    simp
section
variable {U:Type}[Fintype U](q: Matrix U U ℝ)
lemma bleat_pow (p:Pce U)(n r:ℕ): marble r ((press q ^ n : Module.End ℝ _) p) = bleat q (fun i=>marble i p) n r:= by
    induction n generalizing r with
    | zero=> rfl
    | succ n ih=>rw [pow_succ',Module.End.mul_apply,marble_stare,ih];rfl
lemma roaming (p:Pce U)(u r:ℕ)(hx:∀ m>u,marble m p=0) : marble r (hearth q p)=pageant q (fun m=>marble m p) u r:= by
    let N:= max u p.totalDegree; rw [← pageant_growth hx (le_max_left (b:=p.totalDegree) _), padder q p N (le_max_right ..), ← canyon_eq]; unfold pageant; rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,canyon_eq, bleat_pow]
end
end YM.FormalBulk08.Avenue
