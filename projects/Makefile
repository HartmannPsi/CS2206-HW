CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

DIRS = \
	lib

COQ_FLAG = -R $(SL_DIR)SeparationLogic SimpleC.SL -R $(SL_DIR)unifysl Logic -R $(SL_DIR)Asrtdef SimpleC.ASRT -R $(SL_DIR)AuxiFun SimpleC.ASRTFUN -R $(SL_DIR)Cdef SimpleC.CSE -R $(SL_DIR)sets SetsClass -R $(SL_DIR)compcert_lib compcert.lib -R $(SL_DIR)auxlibs AUXLib -R $(SL_DIR)MonadLib StateMonad -R $(SL_DIR)MonadLib/monadnrm StateMonad.monadnrm -R $(SL_DIR)MonadLib/monaderror StateMonad.monaderror -R $(SL_DIR)fixedpoints FP -R $(SL_DIR)Common SimpleC.Common -R $(SL_DIR)CoreLang SimpleC.CoreLang -R $(SL_DIR)Frontend SimpleC.Frontend -R $(COMMON_STRATEGY_DIR) SimpleC.EE -R . SimpleC.EE -R ./lib SimpleC.EE

DEP_FLAG = -R $(SL_DIR)SeparationLogic SimpleC.SL -R $(SL_DIR)unifysl Logic -R $(SL_DIR)Asrtdef SimpleC.ASRT -R $(SL_DIR)AuxiFun SimpleC.ASRTFUN -R $(SL_DIR)Cdef SimpleC.CSE -R $(SL_DIR)sets SetsClass -R $(SL_DIR)compcert_lib compcert.lib -R $(SL_DIR)auxlibs AUXLib -R $(SL_DIR)MonadLib StateMonad -R $(SL_DIR)MonadLib/monadnrm StateMonad.monadnrm -R $(SL_DIR)MonadLib/monaderror StateMonad.monaderror -R $(SL_DIR)fixedpoints FP -R $(SL_DIR)Common SimpleC.Common -R $(SL_DIR)CoreLang SimpleC.CoreLang -R $(SL_DIR)Frontend SimpleC.Frontend -R $(COMMON_STRATEGY_DIR) SimpleC.EE -R . SimpleC.EE -R ./lib SimpleC.EE

lib_FILES = \
	 super_poly_sll2.v

# VC_code_FILE_NAME = \
# 	 functional_queue \
# 	 poly_sll \
# 	 sll_auto \
# 	 sll \
# 	 sll_merge_rel \
# 	 sll_split_while \
# 	 sll_insert_sort 

# strategy_FILE_NAME = \
# 	 functional_queue \
# 	 poly_sll \
# 	 sll_shape \
# 	 sll \
# 	 sll_queue 

# VC_code_proof_FILES = \
#   $(VC_code_FILE_NAME:%=VC/%_goal.v) \
#   $(VC_code_FILE_NAME:%=VC/%_proof_auto.v) \
#   $(VC_code_FILE_NAME:%=VC/%_proof_manual.v) \
#   $(VC_code_FILE_NAME:%=VC/%_goal_check.v) \

# strategy_proof_FILES = \
# 	$(strategy_FILE_NAME:%=VC/%_strategy_goal.v) \
# 	$(strategy_FILE_NAME:%=VC/%_strategy_proof.v) \
# 	$(strategy_FILE_NAME:%=VC/%_strategy_goal_check.v) \

FILES = \
  $(lib_FILES:%.v=lib/%.v) \
  # $(strategy_proof_FILES:%.v=%.v) \
  # $(VC_code_proof_FILES:%.v=%.v) \




$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v


lib : $(lib_FILES:%.v=lib/%.vo)
	@echo Making lib



all : $(FILES:%.v=%.vo)

lib_clean:
	@rm -f lib/*.glob
	@rm -f lib/*.vo
	@rm -f lib/*.vok
	@rm -f lib/*.vos
	@rm -f lib/*.aux

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f */*.glob
	@rm -f */*.vo	
	@rm -f */*.vok 	
	@rm -f */*.vos	
	@rm -f */.*.aux	
	@rm -f .depend


.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend

-include $(DEPS)