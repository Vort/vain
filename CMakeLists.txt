cmake_minimum_required(VERSION 3.25)

project(vain)

include_directories(${CMAKE_SOURCE_DIR})
FILE(GLOB SRC ${CMAKE_SOURCE_DIR}/*.cpp)

if(WIN32)
  set(OPENSSL_USE_STATIC_LIBS ON)
endif()

find_package(Threads REQUIRED)
find_package(OpenSSL REQUIRED)

add_executable("${PROJECT_NAME}" ${SRC})

if(NOT MSVC)
  set_target_properties("${PROJECT_NAME}" PROPERTIES LINK_FLAGS "-static")
endif()

target_link_libraries("${PROJECT_NAME}" OpenSSL::Crypto Threads::Threads ${CMAKE_REQUIRED_LIBRARIES})