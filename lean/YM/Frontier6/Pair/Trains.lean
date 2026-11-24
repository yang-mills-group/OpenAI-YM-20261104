import YM.Work.B15
import YM.Work.B16
import YM.Work.B17
import YM.Next.UV_STRESS.Tiles
import YM.Work.B05

/-! Multiple-cell power trick, using the same even translations as for B16,
keeping the *fixed exterior* data in each copy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Platform
open Set Filter Function MeasureTheory Lattice Cells Wilson Extraction Spec Bid Work.B15 Next.UVStress OS OS.Ground
open scoped Topology BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {n : Side}
lemma addr_more (T:Tiling n) (x:T.Cell) (t j:ℕ) : T.omega (addr T t j+x)=T.omega x:=by
    refine Signed.ext rfl ?_; ext i
    change decide _ = decide _; have hp : T.parity (addr T t j i) = 0:=by rw [addr_apply,Tiling.parity,map_natCast]; simp [show (2:ZMod 2)=0 from rfl];
    rw [Pi.add_apply,T.parity_add,hp,zero_add]
lemma over_even (T:Tiling n) (x:T.Cell) (t j:ℕ) (f: Config G n→ℂ)(U) :
    T.copy (addr T t j+x) f U=T.copy x f (translate (T.units.root (addr T t j)) U):=by
    classical
    let b:= T.units.root (addr T t j); have hh: T.hand (addr T t j+x) ↔ T.hand x:=by rw [Tiling.hand,Tiling.hand,addr_more]
    have hv:T.translateBy (addr T t j+x)=T.translateBy x+b:=by
       unfold Tiling.translateBy Tiling.starts Tiling.bias; rw [map_add,addr_more]; abel
    have ht: pull (T.omega x) (T.translateBy x+b) U=pull (T.omega x) (T.translateBy x) (translate b U):=by rw [← pull_one, pull_pull]; simp [affine]
    simp only [Tiling.copy,hh,hv,addr_more]; rw [ht]
lemma starCopy (T:Tiling n) (x:T.Cell) (f:Config G n → ℂ) U : star (T.copy x f U)=T.copy x (fun U=>star (f U)) U := by unfold Tiling.copy;split <;> rfl

variable {F:Extraction.Order}{k b : ℕ}{I:Type*}[Fintype I] (E : Episode C F k) (u:I→Cover) (hu:Injective u) (hF:b ≤ k)
variable {S:Table C.book}
set_option quotPrecheck false
local notation "Y"=> C.S

include hu C b in
lemma widen_addr (m:ℕ) : ∀ᶠ t:ℕ in atTop, Injective (fun v:Fin m × I => diag t v.1.val+u v.2) := by
   have he (i j:Fin m)(hi:i≠j) (a l:I):∀ᶠ t:ℕ in atTop, diag t i.val+u a ≠ diag t j.val+u l:= by
      filter_upwards [Work.B16.steps_apart (C:=C) (show b ≤ b from le_rfl) (show i.val ≠ j.val from fun h => hi (Fin.ext h)) (u a 0) (u l 0) 0] with t ht
      intro h; apply ht
      have he (v:ℕ):Episode.step C (show b ≤ b from le_rfl) t v=diag t v:=by ext x; unfold Episode.step diag; simp [Schedule.toDepth, Schedule.steps] -- maybe
      rw [he,he]; rw [add_comm,add_comm (u l 0)]; exact congr_fun h 0
   filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr fun j=> eventually_all.mpr fun hi=> eventually_all.mpr fun a=>eventually_all.mpr (he i j hi a))] with t hp
   rintro ⟨i,a⟩ ⟨j,l⟩ h; by_cases he:i=j
   · subst j; exact congr_arg (Prod.mk i) (hu (add_left_cancel h))
   exact False.elim (hp i j he a l h)
include hu in
lemma addresses_expand (m:ℕ) : ∀ᶠ t:ℕ in atTop, ∀ᶠ i:ℕ×ℕ in F.fuse, ∀ h:b ≤ i.1,
    let T:= center C.S i.2 h 0
    Injective (fun v: Fin m × I => addr T t v.1.val + wrap T.period (u v.2)) := by
   filter_upwards [widen_addr (C:=C) (b:=b) u hu m] with t ht
   rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually (sparse C.S b _ ht)] with p hp
   apply Eventually.of_forall; intro N h T
   change Injective (fun v:Fin m × I => wrap T.period (diag t v.1.val)+wrap (T.period) (u v.2))
   simp_rw [← map_add]; exact hp

structure SplitBoard (b N p:ℕ) (X : Config G (C.side N p)→ℂ) (u:I→Cover)(ε:I→ℝ): Prop where
   split : ∃ (hb:b ≤ N)(g:I→Config G (C.side N p)→ℂ),
     let T:=center C.S p hb 0
     (∀ i, Interior (T.chamber 0) (g i) ∧ T.rootTest (C.beta N p) (g i) ≤ ε i) ∧
       X= (fun U=> ∏ i:I, T.copy (wrap (C.side b p) (u i)) (g i) U)

include hu in
lemma multicell_train {ℱ:Filter (ℕ×ℕ)} (s:Seed C F S) (h:ℱ ≤ F.fuse) (ε:I→ℝ) (hp:∀ᶠ i:ℕ×ℕ in ℱ, SplitBoard (C:=C) b i.1 i.2 (E.cuts i.1 i.2 0) u ε) (m:ℕ) :
    ∀ᶠ t:ℕ in atTop, ∀ᶠ i:ℕ×ℕ in ℱ, ‖E.fromCut hF t m i.1 i.2‖ ≤ (∏ j, ε j)^(2*m) := by
   filter_upwards [addresses_expand (C:=C) (b:=b) (F:=F) u hu (2*m)] with t ht
   filter_upwards [hp,Eventually.filter_mono h ht,Eventually.filter_mono h (large_mesh F k)] with i hP hg hN
   obtain ⟨N,p⟩:= i; change k ≤ N at hN
   let T:= center C.S p (hF.trans hN) 0; let Ω:=Config G (C.side N p); let n:Fin (2*m)→T.Cell:= fun j=> addr T t j.val
   obtain ⟨hv,g,hg',hU⟩:=hP.split
   let v (x:Fin (2*m)×I):Ω→ℂ := if x.1.val%2=0 then fun U=> star (g x.2 U) else g x.2
   let c (x:Fin (2*m)×I):T.Cell:= n x.1 + wrap T.period (u x.2)
   let β:= C.beta N p
   have he (x) : Interior (T.chamber 0) (v x) ∧ T.rootTest β (v x) ≤ ε x.2:=by
      unfold v; split
      · rw [rootTest_star]; exact ⟨(hg' x.2).1.real, (hg' x.2).2⟩
      exact hg' x.2
   have hX (U) : E.twice hF t m N p U=∏ x:Fin (2*m)×I,T.copy (c x) (v x) U:=by
      unfold Episode.twice; rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl; intro j _
      have hx(j:Fin (2*m)): T.units.root (n j)=location C.S k N p (Episode.step C hF t j.val):=addr_root C hF hN ..
      rw [← cuts_translate E N p (Episode.step C hF t j.val) U,hU,← hx]; by_cases h:j.val%2=0
      · simp only [h,↓reduceIte,star_prod]; apply Finset.prod_congr rfl; intro q _; rw [show v (j,q)=fun U=> star (g q U) from if_pos h,starCopy]; exact (over_even ..).symm
      simp only [h,↓reduceIte]; apply Finset.prod_congr rfl; intro q _; rw [show v (j,q)=g q from if_neg h]; exact (over_even ..).symm
   change ‖moment β _‖ ≤ _; simp_rw [show E.twice hF t m N p= _ from funext hX]
   apply le_trans (T.planted (s.copies.all N p) c (hg hv) v (fun i=> (he i).1))
   calc
     _ ≤ ∏ x:Fin (2*m) × I, ε x.2:= Finset.prod_le_prod (fun _ _ => T.root_nonneg _ _) (fun x _=> (he x).2)
     _ = _:= by rw [Fintype.prod_prod_type]; simp
open Org
include hu hF
lemma board_character {V:OS.Chamber S timeAxis}{A:Spread V} {ℱ:Filter (ℕ×ℕ)} [ℱ.NeBot] (K:A.Resolution) (z:K.X)
    (s:Seed C F S)(ht:Theme V A)(he:OS.Ground.Steady V)(hs:Phase.reflects (C:=C) V A)(hk:K.Out)
    (h:ℱ ≤ F.fuse) (ε:I→ℝ) (hε:∀ i,0 ≤ ε i)
    (hp:∀ᶠ i:ℕ×ℕ in ℱ, SplitBoard (C:=C) b i.1 i.2 (E.cuts i.1 i.2 0) u ε): ‖K.character z (E.cluster A)‖ ≤ ∏ j, ε j:=by
    refine Retain.bit _ hk _ _ (Finset.prod_nonneg fun i _=> hε i) ?_ z
    intro m
    refine le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp (Work.B17.answer s V A ht he hs b k hF E m)) ?_
    filter_upwards [Work.B16.answer s hF E m,multicell_train E u hu hF s h ε hp m] with t hP hg
    refine le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp (hP.mono_left h)) ?_
    exact hg.mono (fun i H => (Complex.re_le_norm _).trans H)
end YM.Frontier6.Platform
