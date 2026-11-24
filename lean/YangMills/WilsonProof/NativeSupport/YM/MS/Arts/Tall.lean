import YM.MS.Arts.Tall
import YangMills.WilsonProof.NativeSupport.YM.MS.Arts.Meter
/-!
# Dimension weight: affinity of unintegrated trace

Charge traces after ordinary polarized coefficient tests, not tensor alge assumptions.
 Sym group already all extra directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Pilot Spin
open scoped Topology ContDiff
variable {G:Gauge}{R A:Type}[Fintype A][DecidableEq A]{m n k:ℕ}{b:Bool}{F:Mob G}{U:Rip G}
variable {i j: Apart m n}{s t:Bool}{c d:G.ColorIndex} {x:SectorP m}{l: Legs (Shore G m)}
variable (HF:Sturdy b F)(HU:Ruddy b U)
include HF HU
lemma fleck_ext (h:m≤n): fleck h U F i i s t c d x l=token U F s t c d x l := by
    have hv:m<n:= by have hε:=i.isLt; unfold GlyphA at hε; omega
    rw [fleck_moves HF HU h (i:=i) (j:=step hv)]; unfold token fleck; let r := rises (Nat.succ_le_of_lt hv); let z := hatch (Nat.lt_succ_self m); let y:= hatch hv; have hx:r z=y:= hatch_ext (Nat.lt_succ_self m) (Nat.succ_le_of_lt hv)
    let il:=Nat.le_succ m; let V:= Nat.succ_le_of_lt hv; have he {x:SectorP m}: Left h x=Left V (Left il x):= (sons (rises il) r x |>.trans (by unfold r; rw [rides_link])).symm -- simp
    have hz {s:Bool}{c:G.ColorIndex}: vleg s y c=embA r (vleg s z c):= by rw [← hx]; rfl
    change U n (vleg s y c) (vleg t y d) _ * F n ((vleg s y c,_)::(vleg t y d,_)::lift h l)=U _ (vleg s z c) (vleg t z d) _ * F _ ((vleg s z c,_)::(vleg t z d,_)::_); rw [he, hz (s:=s),hz (s:=t), HU.grows V]; rw [← map_neg,← lifts_link il V]; congr 1; exact HF.grows V ((vleg s z c,Left il x)::(vleg t z d,-Left il x)::lift il l)

-- wrapper per l trc extra
private def pot (U:Rip G)(F:Mob G)(k:ℕ)(i j:Cfield G k)(p:SectorP k)(l:Legs (Shore G k)): ℂ:= U k i j p * F k ((i,p)::(j,-p)::l)
lemma vault_n (h:m≤n): trc (U n) (Left h x) (F n) (lift h l)=trc (U m) x (F m) l+(GlyphA m n:ℕ) • yeast U F x l:= by
    let V (i:Cfield G m):= embA (rises h) i; let W := fun (p:Apart m n) s (c:G.ColorIndex)=> vleg s (aside h p) c
    let X i j:= pot U F n i j (Left h x) (lift h l); let Y i j:=pot U F m i j x l
    have hx (i j:Cfield G m): X (V i) (V j)=Y i j:=by
        unfold X Y V pot; rw [HU.grows h i j x]; congr 1; rw [← map_neg]; exact HF.grows h ((i,x)::(j,-x)::l)
    have hV (i:Cfield G m) (p:Apart m n)(s:Bool)(c:G.ColorIndex): X (V i) (W p s c)=0:=by
        unfold X V W pot; rw [← map_neg]; exact mul_eq_zero_of_right _ (vanish_one h HF [(i,x)] l p (-x) c s) -- a prefix ok
    have hy (i:Cfield G m)(p:Apart m n)(s:Bool)(c:G.ColorIndex): X (W p s c) (V i)=0:=by unfold X V W pot; rw [← map_neg]; exact mul_eq_zero_of_right _ (vanish_one h HF [] ((i,-x)::l) p x c s)
    have he (p q:Apart m n)(s t:Bool)(c d:G.ColorIndex): X (W p s c) (W q t d)=if p=q then token U F s t c d x l else 0:= by
          split; · subst q; exact fleck_ext HF HU h;
          exact fleck_zero HF h (by assumption)
    rw [at_trc,at_trc]; change (∑ i:Cfield G n,∑ j:Cfield G n,X i j)=(∑ i:Cfield G m,∑ j:Cfield G m,Y i j)+_; rw [more h]; simp_rw [show ∀ i,(∑ j:Cfield G n,X i j)= (∑ j:Cfield G m,X i (V j))+(∑ p:Apart m n,∑ s,∑ c,X i (W p s c)) from fun i=> more h (X i)]; -- uses V/W reduce exterior
    change (∑ i:Cfield G m,((∑ j:Cfield G m,X (V i) (V j))+(∑ p:Apart m n,∑ s,∑ c,X (V i) (W p s c))))+(∑ p:Apart m n,∑ s,∑ c, ((∑ j:Cfield G m,X (W p s c) (V j))+(∑ q:Apart m n,∑ t,∑ d,X (W p s c) (W q t d)))) = _; simp only [hx,hV,hy,he,Finset.sum_const_zero,zero_add,add_zero];
    simp [yeast] -- rewrite ∑q first with h 
-- define track from this and proof extend point z
lemma tallyN (h:m≤n): Wtr n U F x l=trc (U n) (Left h x) (F n) (lift h l):= by rw [vault_n HF HU h]; unfold Wtr; rw [Pi.add_apply,Pi.smul_apply, ← Nat.cast_smul_eq_nsmul ℂ]; congr 2; unfold GlyphA; simp only [Nat.cast_mul,Nat.cast_sub h,Nat.cast_ofNat]
-- W z affine beat. No analytic
omit HF HU in
lemma combo (z:ℂ)(n:ℕ): Wtr z U F x=Wtr n U F x+(z-n) • (Wtr (n+1:ℕ) U F x-Wtr n U F x):= by unfold Wtr; push_cast; module
lemma trucks (h:m≤n)(z:ℂ): Wtr z U F (Left h x) (lift h l)= Wtr z U F x l:= by
    have hh (k:ℕ) (hi:n≤k): Wtr k U F (Left h x) (lift h l)= Wtr k U F x l:= by rw [tallyN HF HU hi,tallyN HF HU (h.trans hi),lifts_link h hi,show Left hi (Left h x)=Left (h.trans hi) x from (sons (rises h) (rises hi) x).trans (by rw [rides_link])]
    rw [combo (m:=n) z n,combo (m:=m) z n]; simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,hh n le_rfl,hh (n+1) (by omega)]
-- rotation invariance of Wtr
lemma twirls (K:Spin (L m))(hz: K.within b)(z:ℂ): (flagS K G).beam (Wtr z U F (K.turn x))=Wtr z U F x:=by
    funext l; have ht (i:ℕ)(he:m≤ i): (flagS K G).beam (Wtr i U F (K.turn x)) l=Wtr i U F x l:= by
        let V:=arch he K; have hh := arch_steady he K hz; rw [tallyN HF HU he];
        have hV := (HU.turn i V hh).shuttle0 (Left he x) (F i); rw [HF.turn i V hh, show (flagS V G).volp (Left he x)=_ from arch_on he K x] at hV; rw [← hV, Spin.telescopeS he K _ l]; congr! 2; -- risk
        rename_i w; exact tallyN HF HU he
    simp only [combo z m,map_add,map_smul,map_sub,Pi.add_apply,Pi.smul_apply,Pi.sub_apply]; rw [ht m le_rfl,ht _ (by omega)]
end YM.MS.Arts
