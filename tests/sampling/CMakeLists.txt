add_test(NAME sampling-models
    COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/test_models.py
            $<TARGET_FILE:stp-bin> -v
)
set_tests_properties(sampling-models PROPERTIES TIMEOUT 120)
