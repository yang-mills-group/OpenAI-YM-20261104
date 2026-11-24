import YM.OPE.Yarn.Duplicates
/-!
# Declare a mark resource and custom Drive at one inside match
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "h*" => C.path.levels.clock.hatBeta
local notation "V" => Site (C.side m p)
variable {F:I→ Config G (C.side N p)→ℂ}{o:I→ ∀ i:ℕ, Site (C.side i p)}{w:I→ℝ}{u:I→Pod}{v:J→Pod} {d₀:Finset I}{Y:I→∀ i:ℕ,Lamp G (C.side i p)}{X:I→Lamp G (C.side k p)}
include H
section customs
variable {hm:m≤k} {hn:k≤N} (i:I) {P':∀ i:ℕ,Lamp G (C.side i p)} {a:ℝ}
namespace CrewBook
omit H in
lemma realloc {p':I→ Config G (C.side N p)→ℂ}{d':Finset I} {Z:Lamp G (C.side k p)}(hr:CrewBook C N p m k D hm hn F d₀ o u w Y X)(ha:0<a)(hv: Drive C.path j k N p (o i) (stair η a j) D P' hn)(hh:P' k=Z)
     (hw:∃ Q', Wagon C N p m k hm hn Q' p' d' (fun i=>o i k) (Function.update X i Z) (Function.update (fun i=>pocket C (u i) k 1 (w i)) i (stair η a j k))) : CrewBook C N p m k D hm hn p' d' o (Function.update u i (some j)) (Function.update w i a) (Function.update Y i P') (Function.update X i Z):=by
    obtain ⟨Q,hQ⟩:=hw; refine ⟨⟨Q, ?_⟩,fun j=>by by_cases hj:j=i; subst j; rwa [Function.update_self]; rw [Function.update_of_ne hj]; exact hr.serves _,?_,?_⟩
    · convert! hQ using 1; ext1 v; by_cases hp:v=i; subst v; rw [Function.update_self,Function.update_self, Function.update_self]; rfl; simp only [Function.update_of_ne hp]
    · intro v n hp; by_cases he:v=i; subst v; simp only [Function.update_self,Option.some_inj] at *; exact hp ▸ And.intro hh.symm hv; simp only [Function.update_of_ne he] at hp ⊢; exact hr.issued _ _ hp
    intro v hp; by_cases he:v=i; subst v; simp at hp; simp only [Function.update_of_ne he] at hp ⊢; exact hr.rest v hp
lemma intervene (hr:CrewBook C N p m k D hm hn F d₀ o u w Y X)(ha:0<a)(hv: Drive C.path j k N p (o i) (stair η a j) D P' hn)(hh:P' k=X i)(he:stair η a j k ≤ pocket C (u i) k 1 (w i)) : CrewBook C N p m k D hm hn F d₀ o (Function.update u i (some j)) (Function.update w i a) (Function.update Y i P') X:=by
    obtain ⟨Q,hQ⟩:=hr.ready; let w' i:= pocket C (u i) k 1 (w i)
    let a':=stair η a j k; have hx(v): Function.update w' i a' v ≤ w' v:=by by_cases hp:v=i; subst v; rw [Function.update_self]; exact he; rw [Function.update_of_ne hp]
    have hz: Function.update X i (X i)=X:=by ext1 v; by_cases hp:v=i <;> simp [Function.update,hp]
    refine hz ▸ CrewBook.realloc i hr ha hv hh ⟨Q,?_⟩
    rw [hz]; apply hQ.shorten _ hx; intro j; by_cases he:j=i; subst j; rw [Function.update_self]; exact H.protectors _ ha _ _
    rw [Function.update_of_ne he]; exact hQ.fleet.secure _
lemma additive (hr:CrewBook C N p m k D hm hn F ∅ o u w Y X) {f:Config G (C.side k p)→ℂ} (ha:0<a)(hv: Drive C.path j k N p (o i) (stair η a j) D P' hn)(hh:(P' k).watch=(X i).watch + f)(he:(P' k).rays (R k)= (X i).rays (R k))(hq:stair η a j k ≤ pocket C (u i) k 1 (w i))
    (hf:Interior (GridApprox.window 0 (lensScope C d)) f)(hR: GridApprox.room C.path.levels m k (lensScope C d)) : CrewBook C N p m k D hm hn (Function.update F i (F i+GridApprox.backTo C.path N p hn f)) {i} o (Function.update u i (some j)) (Function.update w i a) (Function.update Y i P') (Function.update X i (P' k)):=by
    obtain ⟨Q,hQ⟩:=hr.ready; obtain ⟨Q',hP⟩:= Wagon.sketch i hQ hf hR hh he; refine CrewBook.realloc i hr ha hv rfl ⟨_, hP.shorten (fun v=> ?_) (fun v=> ?_)⟩
    · by_cases hp:v=i; subst v; rw [Function.update_self]; exact H.protectors _ ha _ _
      rw [Function.update_of_ne hp]; exact hQ.fleet.secure _
    by_cases hp:v=i; subst v; rw [Function.update_self]; exact hq
    rw [Function.update_of_ne hp]
end CrewBook
end customs
section prime
def tarred (C:Family G)(k:ℕ)(x:ℝ):= x/(16*C.path.levels.clock.hatBeta (k+1))
def earPay (C:Family G)(d k:ℕ)(x:ℝ):= C.S.a (k+1)^d*(C.path.levels.clock.hatBeta (k+1)*(4*(1/x)))
variable (i:I) {X:I→Lamp G (C.side (k+1) p)} {hm:m≤ k+1}{he:k<N}(hp:o i=fun i=>(0:Site (C.side i p))) (hx: C.ref 0 ≤ k)(hr: CrewBook C N p m (k+1) D hm he F d₀ o u w Y X)(hk:C.ref d ≤ k) (hf:u i=none)
include hp hx hr hk hf
lemma primed : let t:= tarred C k (w i);
    ∃ (P':Coefficient (C.labels.level d) (C.side k p))(S:∀ i:ℕ,Lamp G (C.side i p)), Ignite C.path N p k C.params (C.localSection d) P' (earPay C d k (w i)) 0 (S k) ∧ CrewBook C N p m (k+1) D hm he F d₀ o (Function.update u i (some k)) (Function.update w i t) (Function.update Y i S) X:=by
    intro t; let b:=4*(1/w i); let t':=h* (k+1); have ht: 1<t':=(T).fits.delayed _; have hx':= hr.serves i; have hb:0<b:= by unfold b; positivity
    have hw:t*16*t'=w i:=by change w i/(16*t')*16*t'=w i; field_simp
    have hV:t≤w i:= div_le_self hx'.le (show 1≤16*t' by linarith only [ht]); have hT:0<t:= div_pos hx' (show 0<16*t' by positivity)
    have hh:t*b ≤ 1/(4*t'):= by change w i/(16*t')*(4*(1/w i))≤ _; apply le_of_eq; field_simp;ring
    have hy:2*t*(2*b) ≤1:= by have hz: t*b ≤ 1/4 := hh.trans (one_div_le_one_div_of_le (by norm_num) (by linarith only [ht])); linarith only [hz]
    have ht':t*(t'*b) ≤1:=by
        have hb := mul_le_mul_of_nonneg_right hh (zero_le_one.trans ht.le); have he : 1/(4*t')*t'=1/4:=by field_simp -- ring
        rw [he] at hb; linarith only [hb]
    have ht₀: t*(‖((((C.S.block k).val:ℂ)^d)⁻¹)‖*(t'*b)) ≤ 1:=by
       let x:= (C.S.block k).val; suffices hf : ‖(((x:ℂ)^d)⁻¹)‖≤1 from le_trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (mul_nonneg (zero_le_one.trans ht.le) hb.le) hf) hT.le) ht'
       rw [norm_inv,norm_pow,Complex.norm_natCast]; have h:1 ≤ (x:ℝ):= by exact_mod_cast (C.S.block k).pos
       rw [inv_le_one₀ (zero_lt_one.trans_le (one_le_pow₀ h))]; exact one_le_pow₀ h
    obtain ⟨X',hD,P',hI⟩:= Patrol.ignite (p:=p) (X:=X i) H.seed H.cuts.literal he (b:=b) (o:=0) (by rw [embed_origin]; have hx:= hr.rest i hf; rw [hp] at hx; exact hx) ((H.thor.moon N p k hx he).1.propagate) (H.cuts.improves k _ _ _ hk he) (zero_le_one.trans ht.le) (W:=t) hy ht₀
    let S':= Function.update (Function.update (fun (i:ℕ)=> (default:Lamp G (C.side i p))) k X') (k+1) (X i)
    refine ⟨P', S', ?_, hr.intervene H i hT ?_ (Function.update_self ..) ?_⟩ -- resolve updates
    · unfold S'; rw [Function.update_of_ne (Nat.ne_of_lt k.lt_succ_self), Function.update_self]; exact hI
    · unfold S'; apply Drive_first he _ ⟨fun i hi hx=> by omega⟩ -- Nat lt_of_lt_of_le
      have hz := H.stair_factor k k.lt_succ_self le_rfl hT; rw [H.anchor_march hT] at hz; rw [Function.update_self,hp]; rw [embed_origin] at hD; exact hD.lower (H.protectors _ hT _ _) hz
    rw [hf]; have hz := H.stair_factor k k.lt_succ_self le_rfl hT; rw [H.anchor_march hT] at hz; exact hz.trans (hV.trans_eq (one_mul _|>.symm))
end prime
end YM.OPE.Yarn

