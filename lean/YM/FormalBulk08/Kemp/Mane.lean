import YM.FormalBulk08.Kemp.Harps

/-! Winding of conditional cover tensors rooted (mark not canonical free origin!),
including constants. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05
open Lotus Shore Mesa Gorge City Cork Rift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I V J : Type*} {m p r : ℕ} {η θ A B C : ℝ}

def Vent (x : Biglot I) (T : (n:Side)→Tile (Tor n I) r) (η C : ℝ):= ∀ᶠ n in atTop, Knoxville (lake n I) η (Lotus.drip n x) (T n) C
def Kalm (η : ℝ)(x:Biglot I)(K:Tile (Biglot I) r)(T:(n:Side)→Tile (Tor n I) r):= Light K T ∧ ∃ C, Vent x T η C
variable {T S : Tile (Biglot I) r} {P Z : (n:Side)→Tile (Tor n I) r} {x : Biglot I}
lemma Kalm.add (h:Kalm η x T P)(hp:Kalm η x S Z): Kalm η x (T+S) (fun n=>P n+Z n):= by obtain ⟨h,A,hA⟩:=h; obtain ⟨he,B,hB⟩:=hp; exact ⟨fun v=>(h v).add (he v),_,(hA.and hB).mono fun _ h=>h.1.add h.2⟩
lemma Kalm.smul (h:Kalm η x T P)(c:ℝ) : Kalm η x (c • T) (fun n=>c • P n):= by obtain ⟨h,C,H⟩:=h; exact ⟨fun v=>(h v).const_mul _,_,H.mono fun _ hh=>hh.smul _⟩
lemma Kalm.polish (h:Kalm η x T P): Kalm η x (sand T) (fun n=>sand (P n)):= by obtain ⟨h,C,H⟩:=h; exact ⟨fun v=> (Tendsto.div_const (tendsto_finsetSum _ (fun j _=>h _)) _),C,H.mono fun _ hh=>hh.polish⟩
lemma Kalm.larger (h:Kalm η x T P)(e:r=m):Kalm η x (lengthen e T) (fun n=>lengthen e (P n)):=by cases e; exact h
lemma kalm_many {T : V→ Tile (Biglot I) r} {S : V →(n:Side)→Tile (Tor n I) r}(p:Finset V)(h:∀ i∈p,Kalm η x (T i) (S i)): Kalm η x (∑ i∈p,T i) (fun n=>∑ i∈p,S i n):= by
    induction p using Finset.induction with
    | empty=>simp only [Finset.sum_empty]; exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun n=>Knox_zeros _⟩
    | @insert i p hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma palm {m' : Side}{a:Tor m' I}{t:Tile (Tor m' I) r} (h : Knoxville (lake m' I) η a t C) (x: chain (Tor m' I) r): Real.exp (η*herb (lake m' I) a x)*‖t x‖≤C:=by rw [mul_comm]; exact penn_chill x h -- autoImplicit false
lemma Kalm.charges (h:Kalm η x T P)(hs:0≤η): Kith η T P:= by obtain ⟨h,C,H⟩:=h; exact ⟨h,C,H.mono fun _ hn=>penn_bail hn hs⟩

variable [Fintype I]
lemma kalm_stare {K : Tile (Biglot I) (r+1+1)} {T : (n:Side)→Tile (Tor n I) (r+1+1)}
    {q : Biglot I→ Biglot I→ℝ} {M : (n:Side)→ Tor n I → Tor n I → ℝ} (h : Kalm η x K T) (e : Wind q M) (C : ℝ)
    (hs : 0<η) (hp : ∀ᶠ n in atTop, Grate (lake n I) η (M n) C) : Kalm η x (stare q K) (fun n=>stare (M n) (T n)) := by
   obtain ⟨h,B,H⟩:=h; refine ⟨fun v=>?_,_,(H.and hp).mono fun n hh=> knox_stare hh.1 hs.le (hh.2.rough hs.le) hh.2.1⟩
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
       have hh' := hm.rough hs.le k.1 k.2; rw [Real.norm_eq_abs]; linarith
   unfold telescopeTerm; rw [norm_mul,mul_left_comm]; exact mul_le_mul ho (palm hn W) (by positivity) hd
lemma kalm_bond {K : Tile (Biglot I) (m+1)} {T : (n:Side)→Tile (Tor n I) (m+1)}{U : Tile (Biglot I) (p+1)}{S : (n:Side)→Tile (Tor n I) (p+1)}
    {q : Biglot I→ Biglot I→ℝ} {M : (n:Side)→ Tor n I → Tor n I → ℝ} (h : Kith η K T)(hk:Kalm η x U S)(e : Wind q M) (C : ℝ)
    (hs : 0<η) (hp : ∀ᶠ n in atTop, Grate (lake n I) η (M n) C) (hr:∀ n i j,M n i j=M n j i) : Kalm η x (bond q K U) (fun n=>bond (M n) (T n) (S n)):= by
   obtain ⟨h,A,H⟩:=h; obtain ⟨hx,B,H'⟩:=hk; refine ⟨fun v=>?_,_,(H.and (H'.and hp)).mono fun n he=> knox_bond (he.2.2.turn (hr n)) hs.le he.1 he.2.1⟩
   let X := 1/2*((m+1:ℕ):ℝ)*((p+1:ℕ):ℝ); let d:=size x.1; let Y:=X*(C*(A*B))
   obtain ⟨l,hA,hB,hC⟩:=(H.and (H'.and hp)).exists
   have hl:=hA.1; have hz:=hB.1; have hg:=hC.1;have hX:0≤X:=by unfold X; positivity
   let F (t:Biglot I×Biglot I) := Real.exp (η*d)*Y*(coast (η/2) t.1 * coast (η/2) t.2)
   refine jolt_limit (windup I I) (fun n=> weld (M n) (T n) (S n) (Lotus.drip n ∘ v)) (weld q K U v) F ((coast_pair (half_pos hs)).mul_left _) (fun _=> by unfold F Y coast; positivity) (cast_pair h hx e v) ?_
   filter_upwards [H,H',hp] with n hn hu hv k
   let P:=Lotus.drip n ∘ v
   let W:=Gorge.arm P k.1; let R:=Gorge.leg P k.2; let a:= Lotus.drip n x
   let T1:=wide (lake n I) W;let T2:= herb (lake n I) a R; let t:= skit n (k.1.1-k.2.1)
   have he : skit n k.1.1+skit n k.2.1≤2*(T1+T2+t)+2*d := by
      have hb : skit n k.2.1≤ T2+d:= (skit_anchor n (Fin.cons a R) 0 (Fin.succ 0)).trans (Nat.add_le_add_left (skirt n x.1) T2)
      have hm : skit n k.1.1 ≤ t + skit n k.2.1:=by unfold t; apply le_trans _ (skit_add n _ _); rw [sub_add_cancel]
      omega
   refine sloped d (T1+T2+t) n k.1 k.2 _ he ?_ hs.le
   have he := mul_le_mul_of_nonneg_left (mul_le_mul (grove hv k.1 k.2) (mul_le_mul (palmed hn W 0) (palm hu R) (by positivity) hl) (by positivity) hg) hX
   refine le_trans (le_of_eq ?_) he; unfold weld; rw [show clutch (shed (T n) k.1) (shed (S n) k.2) (Lotus.drip n ∘ v)= T n W*S n R from rfl]; simp_rw [norm_mul,half_norm,Nat.cast_add,mul_add η,Real.exp_add]; unfold X; push_cast; rw [Real.norm_of_nonneg (show (0:ℝ)≤(m:ℝ)+1 by positivity),Real.norm_of_nonneg (show (0:ℝ)≤(p:ℝ)+1 by positivity)]; unfold T1 T2 t; ring

lemma pearl_nil (T:Tile V 0)(M:V→J→ℝ) (p:chain J 0)(z:chain V 0): pearl M T p=T z:= by unfold pearl; simp [show ∀ (u:chain V 0),u=z from fun _=>Subsingleton.elim ..]
lemma kalm_stream [Fintype J](i:J){R:Row I J}(hr:R.strip η C)(hp:0≤C)(hs:0<η)(h:Kalm η x T P): Kalm η (x.1,i) (pearl (lands R) T) (fun n=> pearl (R.acts n) (P n)) := by
    have hh:=h.charges hs.le; obtain ⟨h,A,H⟩:=h; refine ⟨?_,1*(A*((Fintype.card J:ℕ)*C)^r),H.mono fun n he=> (quake (m:=r) (A:= (Fintype.card J)*C) (B:= (Fintype.card I)*C) (pier n I J η hs.le) (fun _=> R.acts n) (x:=Lotus.drip n x) (y:=Lotus.drip n (x.1,i)) ?_ he (fun _=>trundle n R hr hp hs.le) (by positivity)).bill⟩; swap
    · show (pier n I J η hs.le).capsule _ _=1; simp [Lotus.pier,Lotus.drip,rinkshine,skit,Gorge.shine,size,Lattice.lift]
    cases r with
    | zero=>
       intro v; let z:chain (Biglot I) 0:=default; rw [pearl_nil _ (lands R) _ z]; apply (h z).congr'; exact .of_forall fun y=> (pearl_nil (P y) (R.acts y) _ _).symm
    | succ u=>exact (Bank.water_pearl hr hh 0 hs hp).1
end YM.FormalBulk08.Kemp
