import YM.MS.Orbit.Glue
/-!
# Wake ∞ absolute high-mode theory agrees with bulk high and actual seeds. Native η param path.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Filter Function Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Rake Flux Cog Wire Book Convolve Program Wilsonian Wind
open scoped Topology ContDiff Interval
variable {G: Gauge} {I W E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{S:Pack G}{v:Team}{ U:Wind.Dec G}{η:I→ℝ}{L:I→Side}{X:Rake.Site G I}
lemma Soul (w:tagSmooth E (BH G) QP)(h:Trail w): ContDiff ℝ ∞ (fun i=> hook lace (walk0 w i)):= by induction w with| nil=> exact contDiff_const| cons a l ih=> exact ContDiff.mul (flag_sm _ (h a (by simp)|>.neg) a.1) ( ih h.rest )
lemma Tpuff {F:Wind.Flow G} (hp:TouchF F): TouchF (fun t=>sleeve lace (F t)) := fun E _ _ f w hw ht=> ( Soul w hw ).mul ( hp E f w hw ht )
lemma sail_ℓ {F:Law G}{h:ℤ}(hp:Limit F h): Limit ( sleeve lace F ) h:=fun i hi=> by rw [sleeve_here,hp i hi,mul_zero]
-- encoding B and raw
abbrev TokenB (G:Gauge)(v:Team)(η:I→ℝ)(n:ℕ)(i:I): Law G:= if n=0 then 0 else sleeve lace ( run ( style G v ( η i ) n))
abbrev Ext (G:Gauge)(S:Pack G)(η:I→ℝ): Glade G I:= fun i t=> sleeve lace ( S (η i) t )
abbrev Scope (G:Gauge)(F:Wind.Dec G)(η:I→ℝ): Rake.Site G I:= fun i=> Ext G (F i) η
lemma feesBuy {d:ℤ}{b:Bool}(h:Fees b d S)(η:I→ℝ): Knits (Ext G S η):= by
    obtain ⟨v,hv⟩:= h.pay; exact ⟨ ⟨ fun i=> Tpuff ( h.stay ( η i ) |>.joint ), fun i t=> Orbit.volt ( h.stay (η i)|>.perk t ) ⟩, v,fun i t=> sail_ℓ ( hv (η i) t) ⟩ -- unused n
lemma tokenCaps (v:Team)(η:I→ℝ)(G: Gauge): Caps (TokenB G v η):= by
   intro n; by_cases hv:n=0; · rw [show TokenB G v η n=0 from funext fun i=> if_pos hv ]; exact knit0 ..
   rw [show TokenB G v η n = fun i=>_ from funext fun i=> (if_neg hv) ]; exact feesBuy (openOrigin _ n (core_circle G v)) η
lemma guarding (G:Gauge)(v:Team)(η:I→ℝ)(L:I→Side)(i:I): FaceGuard L ( TokenB G v η ) i:= by
    intro n; unfold StartB TokenB; split_ifs; rw [map_zero]; exact ⟨ map_zero _ ,Pure.zero⟩ -- syntax
    obtain h:= openOrigin _ n ( core_circle G v )|>.stay (η i); let F:=run ( style G v (η i) n ); exact ⟨ invarBulk (h.perk 0) (h.stand 0 rfl), pureB ( h.turnt 0 ) ⟩ -- typo implicit n.Body.
lemma dawnG (η:I→ℝ)(L:I→Side)(hp:PC G v U): Script ( outside L ) (uniform G I) (TokenB G v η) ( Scope G U η ):= by
   let T:= Scope G U η; refine ⟨?_,fun n hn=>?_⟩; · unfold Scope; rw [ hp.free ]; ext; simp [ Ext ]; -- problem `G` shadow
   have he(i:I):=hp.recu n hn (η i); refine ⟨ fun i=> Eq.trans (congr_arg (sleeve lace) ( he i|>.1 )) (Eq.symm (if_neg hn.ne')), ( show collect ( T n ) from ( feesBuy ( hp.owes n ) η |>.2)), fun i t w=>?_⟩; -- Tβ.Support.Step.Just.F.
   let X:= U n (η i); obtain h:= (hp.owes n).stay (η i); let P:= CPlan (outside L) (uniform G I); let C:= Cpu G t; have hh : P (T n) i t=sleeve lace ( Wiref G X t ):= by
      change Θ_pc false μzone 0 (dope C) ( sleeve lace (X t)) = sleeve lace (Heat.orbit C μzone (X t)); rw [finite_cc μzone (period0 μzone cour0 ( main_f _ ) h.joint), Θ_z, skin_c ]; rfl
   have hx : ( ((2:ℂ)⁻¹) • groups (uniform G I) T T n ) i t= sleeve lace ( path (1/2:ℝ) n 1 U U (η i) t):= by
      rw [ quarterback ]; unfold groups pathU; simp_rw [Pi.smul_apply, Finset.sum_apply,map_smul,map_sum]; push_cast; rw [one_div]; congr 1; refine Finset.sum_congr rfl fun k hk=> ?_; exact D_tree ( Vrev G t ) -- next
   obtain hu:= ( (he i).2 t w ).const_mul ( hook lace w ); convert! hu using 1; simp only [Pi.add_apply]; unfold P T X at hh; unfold T at hx; rw [ hh, hx, sleeve_here,sleeve_here,mul_add ]
end YM.MS.Orbit
