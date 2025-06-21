docker run --rm -it \
-u $(id -u):$(id -g) \
-v /home/riversity/coq/CS2206-spring2025/qualifiedcprogramming-docker/common/:/include/common/ \
-v /home/riversity/coq/CS2206-spring2025/shared/projects/task3/lib/:/include/lib/ \
-v /home/riversity/coq/CS2206-spring2025/shared/projects/lib/:/include/lab/ \
-v /home/riversity/coq/CS2206-spring2025/shared/projects/task3/VC/:/output/ \
-v /home/riversity/coq/CS2206-spring2025/shared/projects/task3/:/input/ \
qcp:latest symexec \
--no-strategy-gen \
--goal-file=/output/thm_apply_goal.v \
--proof-auto-file=/output/thm_apply_proof_auto.v \
--proof-manual-file=/output/thm_apply_proof_manual.v \
--input-file=/input/thm_apply.c \
-I/include/common/ -I/include/lib/ -I/include/lab/