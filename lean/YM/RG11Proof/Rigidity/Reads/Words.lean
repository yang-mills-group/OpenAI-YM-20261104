import YM.RG11Proof.Rigidity.Grams

/-!
# Speak the Wick sector presentations
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Reads
open Maxwell Maxwell.Free Crowd Prism Function Tensor
open scoped BigOperators Topology InnerProductSpace Classical
variable {G:Gauge}

def emits (p : Article G) : WickPol G:= (p.map Dart.write).prod
def canon (C : Cast G): WickPol G:= (C.map (fun i=> (i.1:ℂ) • emits i.2)).sum
def printed (C : Cast G) (t : ℕ) : WickPol G:=(C.map fun i=> if ceilingG i.2=t then (i.1:ℂ) • emits i.2 else 0).sum

lemma emits_real (p : Article G) : realForm (emits p)=emits p := by
  unfold emits; rw [map_list_prod,List.map_map]
  congr 1; apply List.map_inj_left.mpr; exact fun a _=> real_symbol _
lemma star_smul (c : ℂ) (p : WickPol G): realForm (c • p)=(star c) • realForm p:=by simp [realForm,← MvPolynomial.C_mul']
lemma canon_real (C : Cast G): realForm (canon C)=canon C := by unfold canon; rw [map_list_sum,List.map_map]; congr 1; apply List.map_inj_left.mpr; intro a h; change realForm ((a.1:ℂ) • emits a.2)=_; rw [star_smul,emits_real]; simp

lemma ceilings (a : Dart G)(p:Article G): ceilingG (a::p)=2+a.degree+ceilingG p:=by rw [ceilingG,travel,List.map_cons,cargo_step]; rfl
lemma emits_hom (p : Article G): MvPolynomial.IsWeightedHomogeneous scaleW (emits p) (ceilingG p):=by
  induction p with
  | nil=>
    change MvPolynomial.IsWeightedHomogeneous scaleW (1: WickPol G) 0
    exact MvPolynomial.isWeightedHomogeneous_one ℂ scaleW
  | cons a l ih=>
    have ht : emits (a::l)= symbol a.flip.1 a.flip.2 * emits l := by simp [emits,Dart.write,Free.letter]
    rw [ht,ceilings]; rw [add_comm 2]
    exact (symbol_hom a.flip.2 (fun j=>j+2)).mul ih

abbrev top {G : Gauge} (t : ℕ) : WickPol G →ₗ[ℂ] WickPol G := MvPolynomial.weightedHomogeneousComponent scaleW t

lemma prints (Y : Cast G) (i : ℕ) : top i (canon Y)=printed Y i:=by
  induction Y with
  | nil => exact map_zero _
  | cons a p ih=>
    have hh := MvPolynomial.weightedHomogeneousComponent_eq_self (emits_hom a.2)
    change top i ((a.1:ℂ) • emits a.2+ canon p)=(if ceilingG a.2=i then _ else _) + printed p i
    rw [_root_.map_add,ih,map_smul]; split_ifs with h
    · rw [← h, hh]
    rw [show top i (emits a.2)=0 from MvPolynomial.weightedHomogeneousComponent_eq_zero' i _ (fun d hd=> ?_),smul_zero]
    rw [emits_hom a.2 (MvPolynomial.mem_support_iff.mp hd)]; exact h

-- Actual test converted to frame value (real part unnecessary on the probes)
def paint (q : System (G:=G)) (M : Mirror G) : TaylorTower G:= fun j=>∑ c:G.ColorIndex,∑ i:G.ColorIndex, M (c,i) • fill j (unitColor G c) (q i j)
lemma letter_read (q : System (G:=G))(M : Mirror G)(a:Dart G):
    probe (paint q M) a.write = (↑(∑ s:G.ColorIndex, M (a.tone,s)*a.mode (q s a.degree)):ℂ) := by
  unfold Dart.write Free.letter; rw [symbol_test]
  change (↑(a.mode (faceMap _ (cp a.tone) (paint q M a.degree))):ℂ)=_
  simp only [paint,map_sum,map_smul,which, unitPaint,map_smul,smul_eq_mul,ite_mul]
  congr 1; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> ?_; simp [mul_ite]

lemma prints_out (Y : Cast G) (i) (q) (M : Mirror G) : probe (paint q M) (printed Y i)=(topSample Y i q M:ℂ):=by
  have hs (p : List ℝ) : (↑p.sum:ℂ)=(p.map ((↑) : ℝ→ℂ)).sum := map_list_sum Complex.ofRealHom p
  have hp (p : List ℝ) : (↑p.prod:ℂ)=(p.map ((↑):ℝ→ℂ)).prod:= map_list_prod Complex.ofRealHom p
  unfold printed topSample issue; rw [map_list_sum,List.map_map,hs,List.map_map]; congr 1; apply List.map_inj_left.mpr; intro a _
  dsimp only [Function.comp_apply]; split_ifs; swap; simp only [map_zero,mul_zero,Complex.ofReal_zero]
  rw [map_smul,smul_eq_mul,Complex.ofReal_mul,emits,map_list_prod,List.map_map, hp,List.map_map]; congr 2
  apply List.map_inj_left.mpr; intro j _; exact letter_read ..

end YM.RG11.Rigidity.Reads
