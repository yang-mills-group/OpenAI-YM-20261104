import YM.OPE.Compatible.Bower.Dawn
/-!
# Price port & convert, while retaining peers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology BigOperators Classical
variable {X V I J W K: Type}[Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype K][DecidableEq K][Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    {G:Gauge}{C:Family G}{p n N b d k l:ℕ}{A:Allot C}
variable {P: Ensemble V}{P':Ensemble K}{E : Track C.path V p}
open Lights
variable {O: I→ Track C.path V p}{s:I→ℕ} {a w:ℝ}
    {L: Lights A P N p s (n+1) b E O}
set_option quotPrecheck false
local notation "R"=> C.path.rep N p
local notation "F"=> C.labels.level d
local notation "v"=> C.S.a (n+1)^d * (β C (n+1)*(4*(1/a)))
local notation "g"=>badge_fee C a n
private lemma ability (ha:0<a) :
    badge_fee C a n ≤ a ∧ 4*(badge_fee C a n)*(4*(1/a)) ≤ 1∧ badge_fee C a n*(β C (n+1)*(4*(1/a)))≤1:=by
   unfold badge_fee; let t:=β C (n+1); have ht:1≤t:= (β_one ..).le
   change a/(16*t)≤a ∧ _; refine ⟨div_le_self ha.le (by linarith), ?_,?_⟩
   all_goals unfold t at ht; field_simp; nlinarith only [ht,ha]
variable {q:I→ℕ}{E':Track C.path K p}{O':I→ Track C.path K p}{ι:V ↪ K}{χ:Guard (Names K I)}
    {U:I→ Stem K G (C.S.side (n+1) p)}{R':Config G (C.S.side (n+1) p)→ Marker.Poly (Names K I)}
-- specific seat. convert as in `Badge` then cut root. warranty.
lemma warmup (hA:C.Makes) (x:I)(h: Session P' ι L R' U χ E' O')(hq:q x=n)(hx:∀ i,i≠x→ q i=s i)
    (hk:C.ref d≤ n)(ht:n<N)(hE:Migrating C.path n p (n+1) E) (hy:Migrating C.path n p (n+1) (O x))
    (hf:Blade (R (n+1)) ((L.tips x).home P.v) ((L.tips x).oil P.v) (profile (R (n+1)).activities ((L.tips x).gas P.v)) 0 (4*(1/L.asks x)))
    (ha:0<a)(hw:a ≤ L.asks x):
    ∃ y:Coefficient (C.labels.level d) (C.side n p), y.Format 0 C.params (R n) ∧ (F).coeffSize y.x≤ v ∧ y.remBound 0 (R n) (kappa C.path n) v ∧
    ∃ M:Lights A P N p q (n+1) b E O, Session P' ι M R' U χ E' O'∧ M.bottom x=g∧ Stamp (N:=N) P (C.localSection d) (E n) y ((M x).X n)∧ ∀ i,i≠x→ (M i).w=(L i).w∧ (M i).X=(L i).X:=by
    have hv:= badge_pos (C:=C) (j:=n) ha; obtain ⟨hs,hR,hR'⟩:= ability (C:=C) (n:=n) ha
    obtain ⟨a',hb,hU,hW,X',hy',hx',h'⟩:= convert_path A P hk ht hA (show 0 ≤ 4*(1/a) by positivity) hv hR hR'
       ((hE.mare n le_rfl n.lt_succ_self).symm ▸ ((L x).hold.marks (n+1) (L x).hold.clock le_rfl)) (hf.more (mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le ha hw) (by norm_num))) ((hy.mare n le_rfl n.lt_succ_self).trans (L.steered x|>.symm))
    have h'x: ∃ S:Line A P N p (q x) (n+1) b E (O x), S.X n=X'∧ S.X (n+1)= L.tips x ∧ S.w=(fun _=>g):=by
       rw [hq]; let Z:= update (L x).X n X'; have hZ:Z n=X':=update_self ..; have hY: Z (n+1)=L.tips x:=update_of_ne (Nat.succ_ne_self n) X' (L x).X
       refine ⟨⟨Z,fun _=>g,⟨n.le_succ,ht,fun _ _ _=>hv,fun i he hj=>?_,fun i he hj=> ?_,fun i he hi=>?_⟩,?_⟩,hZ,hY,rfl⟩
       · rcases eq_or_ne i n with hi|hi; rw [hi,hZ]; exact hx'.homes
         rw [show i=n+1 from by omega,hY]; exact (L x).hold.marks _ (L x).hold.clock le_rfl
       · rcases eq_or_ne i n with hi|hi; rw [hi,hZ, hy']
         rw [show i=n+1 from by omega,hY,L.steered]
       · obtain rfl:i=n:=by omega
         exact ⟨_, hY.symm ▸ hZ.symm ▸ h'⟩ -- orientation
       exact fun i _ _=>le_mul_of_one_le_right hv.le (one_le_pow₀ (β_one ..|>.le))
    obtain ⟨S,hS,hZ,hY⟩:= h'x; obtain ⟨M,hM,hP,hX⟩:= dock_inlet h x q hx S hZ (show S.w (n+1)≤ _ from (congr_fun hY _).trans_le (hs.trans hw))
    refine ⟨a',hU,hb,hW,M,hM,?_,?_,fun i hi=> ((hX i hi).symm)⟩
    · unfold bottom; rw [hP,hY]
    rw [hP,hS]; exact hx'
end YM.OPE.Allot
